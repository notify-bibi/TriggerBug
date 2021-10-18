

#include "instopt/engine/state_explorer.h"
#include "instopt/helper/z3_target_call.h"
#include "gen_global_var_call.hpp"
#include "instopt/engine/irsb_cache.h"
#include "llvm/ADT/SparseBitVector.h"
#include "instopt/engine/vexStateHelper.h"
#include "instopt/tracer/BlockView.h"
#include <instopt/tracer/CFGTracer.h>


using namespace TR;

namespace {

    class SimpleMem {
        // AST : SVal
        z3::vcontext& ctx;
    public:
        SimpleMem(z3::vcontext& ctx) : ctx(ctx){

        }

        void Ist_Store(sv::tval const& address, sv::tval const& data) {
            llvm::errs() << address.str(true) << " " << data.str(true) << "\n";
            
        };

        sv::tval Iex_Load(const sv::tval& address, int nbits) {
            llvm::errs() << address.str(true) << "\n";
            
        };

        sv::tval Iex_Load(const sv::tval& address, IRType ty) { 
            
            llvm::errs() << address.str(true) << "\n";
        };

    };


    class SimpleRegs {
        z3::vcontext& ctx;
        VRegs regs;
        llvm::SparseBitVector<4096> BitVector;
        StateHelper& statehelper;
    public:
        SimpleRegs(z3::vcontext& ctx, UInt size, StateHelper& statehelper) :ctx(ctx), regs(ctx, size), statehelper(statehelper) {
            const char* prev = statehelper.regOff2name(0);
            UInt prevOff = 0;
            for (UInt o = 1; o < size; o++) {
                auto regName = statehelper.regOff2name(o);
                //llvm::errs() << regName <<"\n";
                if (prev != regName) {
                    std::stringstream st;
                    auto regVal = ctx.bv_const(prev, (o - prevOff)<<3);
                    regs.Ist_Put(o, (Z3_ast)regVal, (UInt)(o - prevOff));
                    prev = regName;
                    prevOff = o;
                }
            }
        };
        void init(UInt offset, UInt nbytes) {
            for (int o = offset; o < offset + nbytes; o++) {
                if (BitVector.test(o)) {
                }
                else {
                    BitVector.set(o);
                }
            }
        }

        void Ist_Put(UInt offset, sv::tval const& ir) { 
            // init(offset, ir.nbits() >> 3);
            regs.Ist_Put(offset, ir);
        }
        sv::tval Iex_Get(UInt offset, IRType ty) { 
            // init(offset, ty2length(ty));
            return regs.Iex_Get(offset, ty);
        }
    };



    class MemoryModeling : public VMemBase {
        friend class StateBase;
        friend class State;
        SimpleMem m_mem;
        SimpleRegs m_regs;

    public:
        MemoryModeling(z3::vcontext& ctx, UInt size, StateHelper& statehelper) : m_mem(ctx), m_regs(ctx, size, statehelper) {};
        void Ist_Store(sv::tval const& address, sv::tval const& data) override { m_mem.Ist_Store(address, data); };
        sv::tval Iex_Load(const sv::tval& address, int nbits) override { return m_mem.Iex_Load(address, nbits); };
        sv::tval Iex_Load(const sv::tval& address, IRType ty) override { return m_mem.Iex_Load(address, ty); };

        void Ist_Put(UInt offset, sv::tval const& ir) override { m_regs.Ist_Put(offset, ir); }
        sv::tval Iex_Get(UInt offset, IRType ty) override { return m_regs.Iex_Get(offset, ty); }

        // StateModeling mode_change() { return StateData<to_ea_nbits>(m_mem, m_regs); };
        virtual ~MemoryModeling() { }
    };

    class SimpleEnvGuest : public EmuEnvironment {
        IR_Manager m_ir_temp; 
        GraphView& gv;
    public:
        //init vex
        SimpleEnvGuest(GraphView& gv, Z3_context ctx, VexArch arch) :EmuEnvironment(arch, 0) , m_ir_temp(ctx), gv(gv){};

        void block_integrity(Addr ea, UInt sz) override {  }
        void set_guest_bb_insn_control_obj() override { }

        //void block_integrity(Addr address, UInt insn_block_delta) override;

        //new ir temp
        virtual void malloc_ir_buff(Z3_context ctx) override { }
        //free ir temp
        virtual void free_ir_buff() override { }
        // guest translate
        irsb_chunk translate_front(HWord guest_addr) override { 

            auto blocks = gv.get_MutiBlocks();
            auto E = blocks.find(guest_addr)->second;
            BlockView& basic_irsb_chunk = E.get()->operator[](0);
            return basic_irsb_chunk.get_irsb_chunk();
        }
        virtual sv::tval& operator[](UInt idx) override { return m_ir_temp[idx]; }
    };

    class StateModeling : State {
    public:
        StateModeling(vex_context& vctx, VexArch guest_arch, StateHelper& statehelper) :State(vctx, guest_arch) {
            auto m = std::make_shared<MemoryModeling>(ctx(), 4096, statehelper);
            set_mem_access(m);
        };
        void explore(GraphView& gv, const BlockView& entry) {
            irsb_chunk irsb_chunk = entry.get_irsb_chunk();
            std::deque<BtsRefType> tmp_branch;
            Addr guest_start = irsb_chunk->get_bb_base();
            State_Tag    status = Running;

            auto iv = std::make_shared<SimpleEnvGuest>(gv, ctx(), VexArchAMD64);
            set_irvex(iv);



            if UNLIKELY(get_delta()) {
                guest_start = guest_start + get_delta();
                set_delta(0);
            }

            Vex_Kind vkd;

            do {
                irsb_chunk = irvex().translate_front(guest_start);
                IRSB* irsb = irsb_chunk->get_irsb();
                ppIRSB(irsb);
                get_trace()->traceIRSB(*this, guest_start, irsb_chunk);
                if (vinfo().is_mode_32()) {
                    vkd = emu_irsb<32>(tmp_branch, guest_start, status, irsb_chunk);
                }
                else {
                    vkd = emu_irsb<64>(tmp_branch, guest_start, status, irsb_chunk);
                }
                get_trace()->traceIrsbEnd(*this, irsb_chunk);
                

            } while (vkd == TR::Vex_Kind::vUpdate);

        }

        ~StateModeling(){

        }
    };



}



void testfd(GraphView& gv, vex_context& vctx, VexArch guest_arch, StateHelper& statehelper, const BlockView& entry) {
    StateModeling SM(vctx, guest_arch, statehelper);
    SM.explore(gv, entry);
}
