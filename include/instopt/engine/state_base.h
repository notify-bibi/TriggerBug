#ifndef KERNEL_HEAD_DEF
#define KERNEL_HEAD_DEF

#include "instopt/engine/engine.h"
#include "instopt/engine/vex_context.h"
#include "instopt/engine/variable.h"
#include "instopt/engine/register.h"
#include "instopt/engine/memory.h"


sv::tval tUnop(IROp, sv::tval const&);
sv::tval tBinop(IROp, sv::tval const&, sv::tval const&);
sv::tval tTriop(IROp, sv::tval const&, sv::tval const&, sv::tval const&);
sv::tval tQop(IROp, sv::tval const&, sv::tval const&, sv::tval const&, sv::tval const&);

union  GuestRegs
{
    VexGuestX86State   x86;
    VexGuestAMD64State amd64;
    VexGuestARMState   arm;
    VexGuestARM64State arm64;
    VexGuestS390XState s390;
    VexGuestMIPS32State mips32;
    VexGuestMIPS64State mips64;
    VexGuestPPC32State ppc32;
    VexGuestPPC64State ppc64;
};

//所有客户机寄存器的ir层的最大长度。建议>=100

typedef struct {
    GuestRegs guest;
    GuestRegs host;
} VexGuestState;

static constexpr int REGISTER_LEN = ALIGN(sizeof(VexGuestState), 0x100);

class VexIRDirty;
namespace TR {



    template<class BState>
    class BranchManager {
        class _Chunk {
            template<class _> friend class BranchManager;
            BranchManager<BState>* m_this;
            _Chunk* m_bk;
            _Chunk* m_fd;
        };

        class Iterator {
            const _Chunk* m_ptr;
            const _Chunk* m_fd;
        public:
            Iterator(const _Chunk* s) :m_ptr(s), m_fd(s->m_fd) {
            }

            inline bool operator!=(const Iterator& src)
            {
                return m_ptr != src.m_ptr;
            }

            inline void operator++()
            {
                m_ptr = m_fd;
                m_fd = m_fd->m_fd;
            }

            inline BState* operator*() {
                return &m_ptr->m_this->m_state;
            }
        };

        BState& m_state;
        _Chunk m_chunk_link;
        _Chunk m_chunk_branch;

        static void link(_Chunk* cs, _Chunk* branch) {
            _Chunk* fd = cs->m_fd;
            branch->m_bk = cs; branch->m_fd = fd;
            cs->m_fd = branch; fd->m_bk = branch;
        };

    public:
        BranchManager(BState& state) :m_state(state) {
            m_chunk_link.m_this = this;
            m_chunk_link.m_bk = &m_chunk_link;
            m_chunk_link.m_fd = &m_chunk_link;
            m_chunk_branch.m_this = this;
            m_chunk_branch.m_bk = &m_chunk_branch;
            m_chunk_branch.m_fd = &m_chunk_branch;
        };

        BranchManager(BState& state, BranchManager<BState>& f_bm) :BranchManager(state) {
            link(&f_bm.m_chunk_branch, &m_chunk_link);
        };

        bool empty() const { return m_chunk_branch.m_bk == &m_chunk_branch; }
        UInt size() const {
            _Chunk* ptr = m_chunk_branch.m_fd;
            UInt i;
            for (i = 0; ptr != &m_chunk_branch; i++, ptr = ptr->m_fd) {};
            return i;
        }
        operator BState& () { return m_state; };

        ~BranchManager() {
            vassert(m_chunk_branch.m_bk == &m_chunk_branch);
            vassert(m_chunk_branch.m_fd == &m_chunk_branch);
            _Chunk* bk = m_chunk_link.m_bk; _Chunk* fd = m_chunk_link.m_fd;
            bk->m_fd = fd;
            fd->m_bk = bk;
        }



        Iterator begin() const {
            return Iterator(m_chunk_branch.m_fd);
        }

        Iterator end() const {
            return Iterator(&m_chunk_branch);
        }
    };


    class TRsolver :public z3::solver {
        friend class BranchChunk;
        bool                    m_solver_snapshot = false;//if solver::push() m_solver_snapshot = true
        std::vector<sbool>        m_asserts;
    public:
        TRsolver(z3::context& c);
        TRsolver(z3::context& c, solver const& src, translate x) : z3::solver(c, src, x) { m_asserts.reserve(2); }
        void push() { m_solver_snapshot = true; z3::solver::push(); }
        void pop() { z3::solver::pop(); m_solver_snapshot = false; }
        bool is_snapshot() { return m_solver_snapshot; }

        std::vector<sbool> const& get_asserts() const { return m_asserts; };

        //不会保存assert到solver,因为在push之前会进行push
        void add(sbool const& e);

        void add(rsbool const& e) { add(e.tos()); }

        void check_if_forget_pop();

        void add_assert(const sbool& assert);

        inline operator Z3_context() { return ctx(); }

        static z3::solver mk_tactic_solver_default(z3::context& c);

        void use_tactic(z3::tactic& t) {
            *(z3::solver*)(this) = t.mk_solver();
        }
    private:
    };

    //Functional programming
    template<typename T = Addr64>
    class InvocationStack {

        typedef typename std::pair<T, T> value_pair_t;
        std::deque<value_pair_t> m_guest_saved_ret;
    public:
        inline InvocationStack() {}
        inline InvocationStack(InvocationStack<T> const& fsk) {
            m_guest_saved_ret = fsk.m_guest_saved_ret;
        }
        inline void push(T call_ptr, T bp/*栈底*/) {
            m_guest_saved_ret.push_back(value_pair_t(call_ptr, bp));
        }
        inline value_pair_t pop() {
            vassert(!m_guest_saved_ret.empty());
            auto r = m_guest_saved_ret.back();
            m_guest_saved_ret.pop_back();
            return r;
        }
        template<typename T> friend bool operator==(InvocationStack<T> const& a, InvocationStack<T> const& b);
        void operator=(InvocationStack<T> const& b) {
            m_guest_saved_ret = b.m_guest_saved_ret;
        }

        void clear() { m_guest_saved_ret.clear(); }
        bool empty() const { return m_guest_saved_ret.empty(); }
        UInt size() const { return m_guest_saved_ret.size(); }
        const std::deque<value_pair_t>& get_guest_saved_ret() const { return m_guest_saved_ret; }
        operator std::string() const;
    };

    class VRegs : public Register {
    public:
        VexGuestState regs_bytes;
        static_assert(offsetof(VexGuestState, guest.x86.host_EvC_FAILADDR) == 0, "error align");

        inline VRegs(z3::vcontext& ctx, UInt size) :Register(ctx, size) {};

        //翻译转换父register
        inline VRegs(Register& father_regs, z3::vcontext& ctx) : Register(father_regs, ctx) {};
    };


    class VMemBase {
    public:
        virtual void Ist_Store(sv::tval const& address, sv::tval const& data) = 0;
        virtual sv::tval Iex_Load(const sv::tval& address, int nbits) = 0;
        virtual sv::tval Iex_Load(const sv::tval& address, IRType ty) = 0;

        virtual void Ist_Put(UInt offset, sv::tval const& ir) = 0;
        virtual sv::tval Iex_Get(UInt offset, IRType ty) = 0;
        virtual ~VMemBase(){}
    };




    class State;

    __declspec(align(16))
    class StateBase {
        friend class VexIRDirty;
        template<int ea_nbits>
        class StateData : public VMemBase {
            friend class StateBase;
            friend class State;
            Mem& m_mem;
            VRegs& m_regs;
        public:
            StateData(Mem& mem, VRegs& regs): m_mem(mem), m_regs(regs){};
            void Ist_Store(sv::tval const& address, sv::tval const& data) override { m_mem.Ist_Store(address.tors<false, ea_nbits>(), data); };
            sv::tval Iex_Load(const sv::tval& address, int nbits) override { return m_mem.Iex_Load(address.tors<false, ea_nbits>(), nbits); };
            sv::tval Iex_Load(const sv::tval& address, IRType ty) override { return m_mem.Iex_Load(address.tors<false, ea_nbits>(), ty); };

            void Ist_Put(UInt offset, sv::tval const& ir) override { m_regs.Ist_Put(offset, ir); }
            sv::tval Iex_Get(UInt offset, IRType ty) override { return m_regs.Iex_Get(offset, ty); }

            template<int to_ea_nbits>
            StateData<to_ea_nbits> mode_change() { return StateData<to_ea_nbits>(m_mem, m_regs); };
            virtual ~StateData() {}
        };
        friend class State;
        static_assert(offsetof(VRegs, regs_bytes) == offsetof(Register, m_bytes), "error align");
        std::atomic_uint32_t m_fork_deep_num;
        std::atomic_uint32_t m_state_id; // deep_num ... state_id
        std::atomic_uint32_t m_z3_bv_const_n;
        std::atomic_uint32_t m_branch_state_id_max = 0; // deep_num ... state_id

        std::string  p_name;
        StateBase*   m_father;
        z3::vcontext m_ctx;   // z3 prove
        vex_info     m_vinfo; // 支持32/64模式切换 
        vex_context& m_vctx;  // state tree 共用一个 vctx
        //当前state的入口点
        HWord        guest_start_ep; // 虚拟 OEP
        //客户机state的eip（计数器eip）
        HWord        guest_start;    // 虚拟 IP
        HWord        m_delta;        // NEXT_IP = CURR_IP + m_delta
        bool         m_dirty_vex_mode = false;
        //DirtyCtx     m_dctx = nullptr;
        //VexArchInfo* vai_guest, * vai_host;

        Bool         m_need_record;
        State_Tag    m_status;       // state状态
        IRJumpKind   m_jump_kd;      // 

        StateBase(vex_context& vctx, VexArch guest_arch);
        StateBase(StateBase& father, HWord gse);
        void read_mem_dump(const char*);
        virtual ~StateBase();
    public:
        std::shared_ptr<spdlog::logger> logger;
        TRsolver solv;
        //客户机寄存器
        VRegs    regs; // GuestRegs map一定一定要在 Register 后面
        //UChar    regs_bytes[REGISTER_LEN];

        //客户机内存 （多线程设置相同user，不同state设置不同user）
        std::shared_ptr<VMemBase> mem_access;
        Mem      mem;
        BranchManager<StateBase> branch;
        ULong insn_count = 0;

        VexGuestState* get_regs_maps();
        inline HWord get_cpu_ip() { return guest_start; }
        inline HWord get_state_ep() { return guest_start_ep; }
        ULong get_cpu_sp();
        //ip = ip + offset
        inline void set_delta(HWord offset) { m_delta = offset; };
        inline HWord get_delta() const { return m_delta; };
        inline void goto_ptr(HWord addr) { m_delta = addr - guest_start; };
        inline State_Tag status() { return m_status; }
        inline void set_status(State_Tag t) { m_status = t; };
        inline IRJumpKind jump_kd() const { return m_jump_kd; }
        inline void set_jump_kd(IRJumpKind kd) { m_jump_kd = kd; }
        void set_level(spdlog::level::level_enum log_level) { logger->set_level(log_level); }

        sv::tval mk_int_const(UShort nbit);
        sv::tval mk_int_const(UShort n, UShort nbit);
        operator std::string() const;

        void read_bin_dump(const char* binDump);

        UInt getStr(std::stringstream& st, HWord addr);

        inline operator z3::context& () { return m_ctx; }
        inline operator z3::vcontext& () { return m_ctx; }
        inline operator Z3_context() const { return m_ctx; }

        inline z3::vcontext& ctx() { return m_ctx; }
        inline vex_context& vctx() { return m_vctx; }
        inline vex_info& vinfo() { return m_vinfo; }
        inline TRsolver& solver() { return solv; }
        std::string get_log_path();



        inline void vIst_Store(sv::tval const& address, sv::tval const& data) { mem_access->Ist_Store(address, data); };
        inline sv::tval vIex_Load(const sv::tval& address, IRType ty) { return mem_access->Iex_Load(address, ty); };
        inline sv::tval vIex_Load(const sv::tval& address, int nbits) { return mem_access->Iex_Load(address, nbits); };

        inline void vIst_Put(UInt offset, sv::tval const& ir) {  mem_access->Ist_Put(offset, ir); }
        inline sv::tval vIex_Get(UInt offset, IRType ty) { return mem_access->Iex_Get(offset, ty); }

        void set_mem_access(std::shared_ptr<VMemBase> m) { mem_access = std::move(m); };

    public:
    // interface 
        virtual StateBase *ForkState(HWord ges) = 0;

        //virtual inline Ke::Kernel& get_kernel() = 0;

        friend std::ostream& operator<<(std::ostream& out, const TR::StateBase& n) { return out << (std::string)n; };
    private:
        void init_logger();

        //virtual TR::State_Tag call_back_hook(TR::Hook_struct const& hs) override { setFlag(hs.cflag); return (hs.cb) ? (hs.cb)(this) : Running; }
        //virtual bool  StateCompression(TR::StateBase const& next) override { return true; }
        //virtual void  StateCompressMkSymbol(TR::StateBase const& newState) override {  };
    };

};

#endif

