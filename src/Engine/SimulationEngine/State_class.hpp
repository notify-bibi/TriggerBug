#ifndef State_class_defs
#define State_class_defs


#include "../engine.hpp"
#include "Variable.hpp"
#include "Register.hpp"
#include "memory.hpp"
#include "tinyxml2/tinyxml2.h"
#include "libvex_init.hpp"
#include "../Thread_Pool/ThreadPool.hpp"


extern void* funcDict(void*);
extern int eval_all(std::vector<Z3_ast>& result, solver& solv, Z3_ast nia);
extern __m256i  m32_fast[33];
extern __m256i  m32_mask_reverse[33];
extern State*	_states[MAX_THREADS];
extern std::mutex global_state_mutex;
extern Bool     TriggerBug_is_init ;



class State;
class GraphView;

typedef struct ChangeView {
    State* elders;
    ChangeView* front;
}ChangeView;



typedef enum :UChar {
    unknowSystem = 0b00,
    linux,
    windows
}GuestSystem;


typedef enum :ULong {
    CF_None = 0,
    CF_ppStmts = 1ull,
    CF_traceJmp = 1ull << 1,
    CF_traceState = 1ull << 2,
    CF_TraceSymbolic = 1ull << 3,
    CF_PassSigSEGV = 1ull << 4,
}TRControlFlags;


typedef struct _Hook {
    TRtype::Hook_CB cb;
    UChar original;
    TRControlFlags cflag;
}Hook_struct;


class StatetTraceFlag {
    friend GraphView;
private:
    static tinyxml2::XMLDocument doc;
    tinyxml2::XMLError err;
    tinyxml2::XMLElement* doc_TriggerBug;
    TRControlFlags traceflags;
public:
        VexArch	guest;
        GuestSystem guest_system;
        const char*   MemoryDumpPath;

        tinyxml2::XMLElement* doc_VexControl;
            VexRegisterUpdates iropt_register_updates_default;
            VexRegisterUpdates pxControl;
            Int iropt_level;
            UInt guest_max_insns;

        tinyxml2::XMLElement* doc_debug;

public:
    StatetTraceFlag(const char* filename):
        err(loadFile(filename)),
        doc_TriggerBug(doc.FirstChildElement("TriggerBug")),
        doc_VexControl(doc_TriggerBug->FirstChildElement("VexControl")),
        doc_debug(doc_TriggerBug->FirstChildElement("DEBUG")),

        guest_system(unknowSystem),
        guest(VexArch_INVALID),
        MemoryDumpPath("��û������ļ�"),

        iropt_register_updates_default(VexRegUpdSpAtMemAccess),
        pxControl(VexRegUpdSpAtMemAccess),
        iropt_level(2),
        guest_max_insns(100),
        traceflags(CF_None)

    {
        gGuestArch();
        gVexArchSystem();
        gMemoryDumpPath();
        gGuestStartAddress();
        gPassSigSEGV();
        gRegsIpOffset();

        if (doc_VexControl) {
            giropt_register_updates_default();
            giropt_level();
            gpxControl();
            gguest_max_insns();
        }
        if (doc_debug) {
            bool traceState = false, traceJmp = false, ppStmts = false, TraceSymbolic = false;
            auto _ppStmts = doc_debug->FirstChildElement("ppStmts");
            auto _TraceState = doc_debug->FirstChildElement("TraceState");
            auto _TraceJmp = doc_debug->FirstChildElement("TraceJmp");
            auto _TraceSymbolic = doc_debug->FirstChildElement("TraceSymbolic");

            if (_TraceState) _TraceState->QueryBoolText(&traceState);
            if (_TraceJmp) _TraceJmp->QueryBoolText(&traceJmp);
            if (_ppStmts) _ppStmts->QueryBoolText(&ppStmts);
            if (_TraceSymbolic) _TraceSymbolic->QueryBoolText(&TraceSymbolic);
            if (traceState) setFlag(CF_traceState);
            if (traceJmp) setFlag(CF_traceJmp);
            if (ppStmts) setFlag(CF_ppStmts);
            if (TraceSymbolic) setFlag(CF_TraceSymbolic);
        }
        
    }

    StatetTraceFlag(StatetTraceFlag& f)
    {
        *this = f;
    }
    inline bool getFlag(TRControlFlags t) const {
        return traceflags & t;
    }

    inline void setFlag(TRControlFlags t) {
        *(ULong*)&traceflags |= t;
    }

    inline void unsetFlag(TRControlFlags t) {
        *(ULong*)&traceflags &= ~t;
    }

    UInt gMaxThreadsNum() {
        UInt    MaxThreadsNum = 16;
        tinyxml2::XMLElement* _MaxThreadsNum = doc_TriggerBug->FirstChildElement("MaxThreadsNum");
        if (_MaxThreadsNum) _MaxThreadsNum->QueryIntText((Int*)(&MaxThreadsNum));
        return MaxThreadsNum;
    }

    UInt gRegsIpOffset() {
        switch (guest) {
        case VexArchX86:return X86_IR_OFFSET::eip;
        case VexArchAMD64:return AMD64_IR_OFFSET::rip;
        case VexArchARM:
        case VexArchARM64:
        case VexArchPPC32:
        case VexArchPPC64:
        case VexArchS390X:
        case VexArchMIPS32:
        case VexArchMIPS64:
        default:
            std::cout << "Invalid arch in vex_prepare_vai.\n" << std::endl;
            vassert(0);
        }
    }


    UInt gtraceflags() {
        tinyxml2::XMLElement* _traceflags = doc_VexControl->FirstChildElement("traceflags");
        if (_traceflags) return _traceflags->IntText();
        return 0;
    }

    ADDR gGuestStartAddress() {
        ULong GuestStartAddress = -1;
        tinyxml2::XMLElement* _GuestStartAddress = doc_TriggerBug->FirstChildElement("GuestStartAddress");
        if (_GuestStartAddress) sscanf(_GuestStartAddress->GetText(), "%llx", &GuestStartAddress);
        return GuestStartAddress;
    }

private:

    tinyxml2::XMLError loadFile(const char* filename) {
        tinyxml2::XMLError error = doc.LoadFile(filename);
        if (error != tinyxml2::XML_SUCCESS) {
            printf("error: %d Error filename %s    at:%s line %d", error,  filename, __FILE__, __LINE__);
            exit(1);
        }
        return error;
    }

    void gGuestArch() {
        auto _VexArch = doc_TriggerBug->FirstChildElement("VexArch");
        if(_VexArch) sscanf(_VexArch->GetText(), "%x", &guest);
    }


    void gMemoryDumpPath() {
        tinyxml2::XMLElement* _MemoryDumpPath = doc_TriggerBug->FirstChildElement("MemoryDumpPath");
        if (_MemoryDumpPath) MemoryDumpPath = _MemoryDumpPath->GetText();
    }

    void gPassSigSEGV(){
        auto _PassSigSEGV = doc_TriggerBug->FirstChildElement("PassSigSEGV");
        bool PassSigSEGV = false;
        if (_PassSigSEGV)_PassSigSEGV->QueryBoolText((bool*)(&PassSigSEGV));
        if (PassSigSEGV) setFlag(CF_PassSigSEGV);
    }


    void gVexArchSystem() {
        tinyxml2::XMLElement* _GuestStartAddress = doc_TriggerBug->FirstChildElement("VexArchSystem");
        if (_GuestStartAddress) {

            if (!strcmp(_GuestStartAddress->GetText(), "linux")) {
                guest_system = linux;
            }
            if (!strcmp(_GuestStartAddress->GetText(), "windows")) {
                guest_system = windows;
            }
            if (!strcmp(_GuestStartAddress->GetText(), "win")) {
                guest_system = windows;
            }
        }
    }

    void giropt_register_updates_default() {
        tinyxml2::XMLElement* _iropt_register_updates_default = doc_VexControl->FirstChildElement("iropt_register_updates_default");
        if (_iropt_register_updates_default) sscanf(_iropt_register_updates_default->GetText(), "%x", &iropt_register_updates_default);
    }

    void gpxControl() {
        tinyxml2::XMLElement* _pxControl = doc_VexControl->FirstChildElement("pxControl");
        if (_pxControl) sscanf(_pxControl->GetText(), "%x", &pxControl);
    }

    void giropt_level() {
        tinyxml2::XMLElement* _iropt_level = doc_VexControl->FirstChildElement("iropt_level");
        if (_iropt_level) iropt_level = _iropt_level->IntText();
    }

    void gguest_max_insns() {
        auto _guest_max_insns = doc_TriggerBug->FirstChildElement("guest_max_insns");
        if (_guest_max_insns) guest_max_insns = _guest_max_insns->IntText();
    }
};


extern Bool chase_into_ok(void* value, Addr addr);
extern void vex_hwcaps_vai(VexArch arch, VexArchInfo* vai);
extern void vex_prepare_vbi(VexArch arch, VexAbiInfo* vbi);
extern void* dispatch(void);
extern UInt needs_self_check(void* callback_opaque, VexRegisterUpdates* pxControl, const VexGuestExtents* guest_extents);
extern void IR_init(VexControl &vc);
extern "C" ULong x86g_use_seg_selector(HWord ldt, HWord gdt, UInt seg_selector, UInt virtual_addr);

class Vex_Info :public StatetTraceFlag {

    friend GraphView;
protected:
    Pap pap;
    VexTranslateResult res;
    VexArchInfo         vai_guest, vai_host;
    VexGuestExtents     vge;
    VexTranslateArgs    vta;
    VexTranslateResult  vtr;
    VexAbiInfo	        vbi;
    VexControl          vc;

private:
    void init()
    {
        LibVEX_default_VexControl(&vc);
        LibVEX_default_VexArchInfo(&vai_host);
        LibVEX_default_VexArchInfo(&vai_guest);
        LibVEX_default_VexAbiInfo(&vbi);

        vbi.guest_amd64_assume_gs_is_const = True;
        vbi.guest_amd64_assume_fs_is_const = True;
        vc.iropt_verbosity = 0;
        vc.iropt_level = iropt_level;
        vc.iropt_unroll_thresh = 0;
        vc.guest_max_insns = guest_max_insns;
        pap.guest_max_insns = vc.guest_max_insns;
        vc.guest_chase_thresh = 0;   //����׷��

        vc.iropt_register_updates_default = iropt_register_updates_default;

        vex_hwcaps_vai(HOSTARCH, &vai_host);
        vex_hwcaps_vai(guest, &vai_guest);
        vai_host.endness = VexEndnessLE;//VexEndnessBE
        vai_guest.endness = VexEndnessLE;//VexEndnessBE

        vex_prepare_vbi(guest, &vbi);
        vta.callback_opaque = NULL;
        vta.preamble_function = NULL;
        vta.instrument1 = NULL;
        vta.instrument2 = NULL;
        vta.finaltidy = NULL;
        vta.preamble_function = NULL;

        vta.disp_cp_chain_me_to_slowEP = (void*)dispatch;
        vta.disp_cp_chain_me_to_fastEP = (void*)dispatch;
        vta.disp_cp_xindir = (void*)dispatch;
        vta.disp_cp_xassisted = (void*)dispatch;

        vta.arch_guest = guest;
        vta.archinfo_guest = vai_guest;
        vta.arch_host = HOSTARCH;
        vta.archinfo_host = vai_host;
        vta.abiinfo_both = vbi;
        vta.guest_extents = &vge;
        vta.chase_into_ok = chase_into_ok;
        vta.needs_self_check = needs_self_check;


        vta.traceflags = gtraceflags();
        vta.pap = &pap;
    }

public:

    Vex_Info(const char* filename):
        StatetTraceFlag(filename)
    {
        init();
    }
    Vex_Info(Vex_Info& f):
        StatetTraceFlag(f)
    {
        init();
    }
};


class BranchChunk {
public:
    ADDR m_oep;
    Vns  m_sym_addr;
    Vns  m_guard;
    bool m_tof;

    BranchChunk(ADDR oep, Vns const& sym_addr, Vns const& guard, bool tof) :
        m_oep(oep),
        m_sym_addr(sym_addr),
        m_guard(guard),
        m_tof(tof)
    {
    }
    State* getState(State& fstate);
};


class State:public Vex_Info {
    friend MEM;
    friend GraphView;
protected:
    static std::hash_map<ADDR, Hook_struct> CallBackDict;
    static std::hash_map<ADDR/*static table base*/, TRtype::TableIdx_CB> TableIdxDict;

    UShort t_index;
    ADDR guest_start_ep;
    ADDR guest_start;
    ADDR guest_start_of_block;
    bool is_dynamic_block;
	void *VexGuestARCHState;

public:
    static Vns ir_temp[MAX_THREADS][400];
    static ThreadPool* pool;
	z3::context m_ctx;
    z3::params m_params; 
    z3::tactic m_tactic;
	z3::solver solv;
	//std::queue< std::function<void()> > check_stack;
	Long delta;
	bool unit_lock;

private:
    bool isTop;
    Bool need_record;
    int replace_const;


	std::vector<Vns> asserts;

	inline Bool treeCompress(z3::context &ctx, Addr64 Target_Addr, State_Tag Target_Tag, std::vector<State_Tag> &avoid, ChangeView& change_view, std::hash_map<ULong, Vns> &change_map, std::hash_map<UShort, Vns> &regs_change_map);
    bool Ist_Exit_find_branch(std::vector<BranchChunk> &branchChunks, Vns const& guard, IRSB *irsb, UInt stmtn);

public:
	Register<REGISTER_LEN> regs;
	MEM mem;//���߳�������ͬuser����ͬstate���ò�ͬuser
	ULong runed = 0;
	std::vector <State*> branch;
    std::vector<BranchChunk> branchChunks;
	State_Tag status;


    State(const char* filename, Addr64 gse, Bool _need_record) ;
	State(State *father_state, Addr64 gse) ;
    void read_mem_dump(const char*);

	~State() ;
    static void thread_register();
    static void thread_unregister();
	inline IRSB* BB2IR();
	void add_assert(Vns &assert, Bool ToF);
    inline void add_assert(Vns& assert) { add_assert(assert, True); };
	inline void add_assert_eq(Vns &eqA, Vns &eqB);
    void start(Bool first_bkp_pass);
    void branchGo();


	void compress(Addr64 Target_Addr, State_Tag Target_Tag, std::vector<State_Tag> &avoid);//�������״̬ 
	inline Vns getassert(z3::context &ctx);
	inline Vns tIRExpr(IRExpr*);
	inline void write_regs(int offset, void*, int length);
	inline void read_regs(int offset, void*, int length);
	inline Vns CCall(IRCallee *cee, IRExpr **exp_args, IRType ty);
    static Vns T_Unop(context & m_ctx, IROp, Vns const&);
    static Vns T_Binop(context & m_ctx, IROp, Vns const&, Vns const&);
    static Vns T_Triop(context & m_ctx, IROp, Vns const&, Vns const&, Vns const&);
    static Vns T_Qop(context & m_ctx, IROp, Vns const&, Vns const&, Vns const&, Vns const&);
	inline Vns ILGop(IRLoadG *lg);

    Vns get_int_const(UShort nbit);
    Vns get_int_const(UShort n, UShort nbit);
    UInt getStr(std::stringstream& st, ADDR addr);
    //read static_table from symbolic address  ���� index �� �ó������� ֮��Ĺ�ϵ ��Ȼz3ֻ����һ���� ��DES��4����̬��
    static inline void idx2Value_Decl_add(Addr64 addr, TRtype::TableIdx_CB func) { TableIdxDict[addr] = func; };
    static inline void idx2Value_Decl_del(Addr64 addr, TRtype::TableIdx_CB func) { TableIdxDict.erase(TableIdxDict.find(addr)); };
    Z3_ast idx2Value(ADDR base, Z3_ast idx);

    inline operator context& () { return m_ctx; }
    inline operator Z3_context() { return m_ctx; }
    inline operator MEM& () { return mem; }
    inline operator Register<REGISTER_LEN>&() { return regs; }
    inline ADDR get_cpu_ip() { return guest_start; }
    inline ADDR get_state_ep() { return guest_start_ep; }
    inline ADDR get_start_of_block() { return guest_start_of_block; }
	operator std::string();


    static void pushState(State& s) {
        pool->enqueue([&s] {
            s.start(True);
            });
    }

    //backpoint add
    void hook_add(ADDR addr, TRtype::Hook_CB func = nullptr, TRControlFlags cflag = CF_None)
    {
        if (CallBackDict.find(addr) == CallBackDict.end()) {
            auto P = mem.getMemPage(addr);
            CallBackDict[addr] = Hook_struct{ func ,P->unit->m_bytes[addr & 0xfff] , cflag };
            P->unit->m_bytes[addr & 0xfff] = 0xCC;
        }
        else {
            if (func){
                CallBackDict[addr].cb = func;
            }
            if (cflag != CF_None) {
                CallBackDict[addr].cflag = cflag;
            }
        }
    }
    bool get_hook(Hook_struct& hs, ADDR addr);
    void hook_del(ADDR addr, TRtype::Hook_CB func);
    //interface :

    virtual inline void   traceStart() { return; };
    virtual inline void   traceFinish() { return; };
    virtual inline void   traceIRSB(IRSB*) { return; };
    virtual inline void   traceIRStmtBegin(IRStmt*) { return; };
    virtual inline void   traceIRStmtEnd(IRStmt*) { return; };

    virtual inline State_Tag Ijk_call(IRJumpKind) { return Death; };
    virtual inline void   cpu_exception() { status = Death; }
    virtual inline State* ForkState(ADDR ges) { return nullptr; }
}; 


template <class TC>
class StatePrinter : public TC {
public:
    StatePrinter(const char* filename, Addr64 gse, Bool _need_record) :
        TC(filename, gse, _need_record)
    {
    };

    StatePrinter(StatePrinter* father_state, Addr64 gse) :
        TC(father_state, gse)
    {
    };


    void spIRExpr(const IRExpr* e);

    void spIRTemp(IRTemp tmp)
    {
        if (tmp == IRTemp_INVALID)
            vex_printf("IRTemp_INVALID");
        else
        {
            vex_printf("t%u: ", tmp);
            std::cout << ir_temp[t_index][tmp];
        }
    }

    void spIRPutI(const IRPutI* puti);
    void spIRStmt(const IRStmt* s);

    void   traceStart() {
        if (getFlag(CF_traceState))
            std::cout << "\n+++++++++++++++ Thread ID: " << GetCurrentThreadId() << "  address: " << std::hex << guest_start << "  Started +++++++++++++++\n" << std::endl;
    };

    void   traceFinish() {
        if (getFlag(CF_traceState))
            std::cout << "\n+++++++++++++++ Thread ID: " << GetCurrentThreadId() << "  address: " << std::hex << guest_start << "  OVER +++++++++++++++\n" << std::endl;

    }
    
    void   traceIRStmtBegin(IRStmt* s) {
        if (getFlag(CF_ppStmts)) {
            ppIRStmt(s);
        }
    };
    void   traceIRStmtEnd(IRStmt* s) {
        if (getFlag(CF_ppStmts)) {
            if (s->tag == Ist_WrTmp) {
                std::cout << ir_temp[temp_index()][s->Ist.WrTmp.tmp] << std::endl;
            }
            else {
                vex_printf("\n");
            }
        }
    };

    void   traceIRSB(IRSB* bb) {
        if (getFlag(CF_traceJmp)) {
            vex_printf("Jmp: %llx \n", guest_start);
        }
    };


    virtual State* ForkState(ADDR ges) {
        return new StatePrinter<TC>(this, ges);
    };

};








#endif



/*Legal parameters are :
  ctrl_c(bool) (default: true)
  dump_benchmarks(bool) (default: false)
  dump_models(bool) (default: false)
  elim_01(bool) (default: true)
  enable_sat(bool) (default: true)
  enable_sls(bool) (default: false)
  maxlex.enable(bool) (default: true)
  maxres.add_upper_bound_block(bool) (default: false)
  maxres.hill_climb(bool) (default: true)
  maxres.max_core_size(unsigned int) (default: 3)
  maxres.max_correction_set_size(unsigned int) (default: 3)
  maxres.max_num_cores(unsigned int) (default: 4294967295)
  maxres.maximize_assignment(bool) (default: false)
  maxres.pivot_on_correction_set(bool) (default: true)
  maxres.wmax(bool) (default: false)
  maxsat_engine(symbol) (default: maxres)
  optsmt_engine(symbol) (default: basic)
  pb.compile_equality(bool) (default: false)
  pp.neat(bool) (default: true)
  priority(symbol) (default: lex)
  rlimit(unsigned int) (default: 0)
  solution_prefix(symbol) (default:)
  timeout(unsigned int) (default: 4294967295)
*/
