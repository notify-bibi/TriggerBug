#ifndef KERNEL_HEAD_DEF
#define KERNEL_HEAD_DEF

#include "engine/engine.h"
#include "engine/vex_context.h"
#include "engine/variable.h"
#include "engine/register.h"
#include "engine/memory.h"


sv::tval tUnop(IROp, sv::tval const&);
sv::tval tBinop(IROp, sv::tval const&, sv::tval const&);
sv::tval tTriop(IROp, sv::tval const&, sv::tval const&, sv::tval const&);
sv::tval tQop(IROp, sv::tval const&, sv::tval const&, sv::tval const&, sv::tval const&);

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
        std::deque<T> guest_call_stack;
        std::deque<T> guest_stack;
    public:
        inline InvocationStack() {}
        inline InvocationStack(InvocationStack<T> const& fsk) {
            guest_call_stack = fsk.guest_call_stack;
            guest_stack = fsk.guest_stack;
        }
        inline void push(T call_ptr, T bp/*栈底*/) {
            guest_call_stack.push_back(call_ptr);
            guest_stack.push_back(bp);
        }
        inline void pop() {
            if (!guest_call_stack.empty()) {
                guest_call_stack.pop_back();
                guest_stack.pop_back();
            }
        }
        template<typename T> friend bool operator==(InvocationStack<T> const& a, InvocationStack<T> const& b);
        void operator=(InvocationStack<T> const& b) {
            guest_call_stack = b.guest_call_stack;
            guest_stack = b.guest_stack;
        }

        void clear() { guest_call_stack.clear(); guest_stack.clear(); }
        bool empty() const { return guest_call_stack.empty(); }
        UInt size() const { return guest_call_stack.size(); }
        const std::deque<T>& get_guest_stack() const { return guest_stack; }
        const std::deque<T>& get_guest_call_stack() const { return guest_call_stack; }
        operator std::string() const;
    };



    class State;

    class StateBase {
        friend class State;

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
        VexArchInfo* vai_guest, * vai_host;

        Bool         m_need_record;
        std::atomic_uint32_t m_z3_bv_const_n;
        State_Tag    m_status;       // state状态
        IRJumpKind   m_jump_kd;      // 

        StateBase(vex_context& vctx, VexArch guest_arch);
        StateBase(StateBase& father, HWord gse);
        void read_mem_dump(const char*);
        virtual ~StateBase();
    public:
        //客户机寄存器
        TRsolver               solv;
        Register<REGISTER_LEN> regs;
        //客户机内存 （多线程设置相同user，不同state设置不同user）
        Mem                     mem;
        BranchManager<StateBase> branch;


        inline HWord get_cpu_ip() { return guest_start; }
        inline HWord get_state_ep() { return guest_start_ep; }
        //ip = ip + offset
        inline void set_delta(HWord offset) { m_delta = offset; };
        inline HWord get_delta() const { return m_delta; };
        inline void goto_ptr(HWord addr) { m_delta = addr - guest_start; };
        inline State_Tag status() { return m_status; }
        inline void set_status(State_Tag t) { m_status = t; };
        inline IRJumpKind jump_kd() const { return m_jump_kd; }
        inline void set_jump_kd(IRJumpKind kd) { m_jump_kd = kd; }

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

    public:
    // interface 
        virtual StateBase* ForkState(HWord ges) { VPANIC("need to implement the method"); return nullptr; }

        //virtual inline Ke::Kernel& get_kernel() { VPANIC("need to implement the method"); return *(Ke::Kernel*)(1); }

    private:

        //virtual TR::State_Tag call_back_hook(TR::Hook_struct const& hs) override { setFlag(hs.cflag); return (hs.cb) ? (hs.cb)(this) : Running; }
        //virtual bool  StateCompression(TR::StateBase const& next) override { return true; }
        //virtual void  StateCompressMkSymbol(TR::StateBase const& newState) override {  };
    };




    bool operator==(InvocationStack<HWord> const& a, InvocationStack<HWord> const& b);

    std::ostream& operator<<(std::ostream& out, const TR::StateBase& n);

    std::ostream& operator << (std::ostream& out, const TR::InvocationStack<HWord>& e);


};

#endif

