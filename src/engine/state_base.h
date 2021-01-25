#pragma once
#ifndef KERNEL_HEAD_DEF
#define KERNEL_HEAD_DEF

#include "engine/engine.h"
#include "engine/vex_context.h"
#include "engine/variable.h"
#include "engine/register.h"

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
        friend class State;
        friend class BranchChunk;
        friend class StateX86;
        friend class StateAMD64;
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
    template<typename HWord>
    class InvocationStack {
        std::deque<HWord> guest_call_stack;
        std::deque<HWord> guest_stack;
    public:
        inline InvocationStack() {}
        inline InvocationStack(InvocationStack<HWord> const& fsk) {
            guest_call_stack = fsk.guest_call_stack;
            guest_stack = fsk.guest_stack;
        }
        inline void push(HWord call_ptr, HWord bp/*栈底*/) {
            guest_call_stack.push_back(call_ptr);
            guest_stack.push_back(bp);
        }
        inline void pop() {
            if (!guest_call_stack.empty()) {
                guest_call_stack.pop_back();
                guest_stack.pop_back();
            }
        }
        template<typename HWord> friend bool operator==(InvocationStack<HWord> const& a, InvocationStack<HWord> const& b);
        void operator=(InvocationStack<HWord> const& b) {
            guest_call_stack = b.guest_call_stack;
            guest_stack = b.guest_stack;
        }

        void clear() { guest_call_stack.clear(); guest_stack.clear(); }
        bool empty() const { return guest_call_stack.empty(); }
        UInt size() const { return guest_call_stack.size(); }
        operator std::string() const;
    };


    class StateBase {
        friend class TR::State;

        z3::vcontext m_ctx;
        vex_info&    m_vex_info;
        //当前state的入口点
        HWord        guest_start_ep;
        //客户机state的eip（计数器eip）
        HWord        guest_start;

        bool         m_dirty_vex_mode = false;
        //DirtyCtx     m_dctx = nullptr;
        VexArchInfo* vai_guest, * vai_host;

        Bool         m_need_record;
        UInt         m_z3_bv_const_n;
        std::mutex   m_state_lock;
        HWord        m_delta;
        State_Tag    m_status;
        IRJumpKind   m_jump_kd;
        InvocationStack<HWord>   m_InvokStack;

    public:
        //客户机寄存器
        TRsolver                 solv;
        Register<REGISTER_LEN>  regs;
        BranchManager<StateBase> branch;

        inline HWord get_cpu_ip() { return guest_start; }
        inline HWord get_state_ep() { return guest_start_ep; }
        //ip = ip + offset
        inline void set_delta(HWord offset) { m_delta = offset; };
        inline void goto_ptr(HWord addr) { m_delta = addr - guest_start; };
        inline State_Tag status() { return m_status; }
        inline void set_status(State_Tag t) { m_status = t; };
        inline IRJumpKind jump_kd() const { return m_jump_kd; }
        inline void set_jump_kd(IRJumpKind kd) { m_jump_kd = kd; }
        inline InvocationStack<HWord>& get_InvokStack() { return m_InvokStack; }

        tval mk_int_const(UShort nbit);
        tval mk_int_const(UShort n, UShort nbit);
        void read_mem_dump(const char*);
        operator std::string() const;

        StateBase(TR::vctx_base& vctx_base, HWord gse, Bool _need_record);

        StateBase(StateBase& father, HWord gse);

        virtual StateBase* ForkState(HWord ges) { VPANIC("need to implement the method"); return nullptr; }
    public:
        std::queue<Z3_ast>  io_buff;

        static tval tUnop(IROp, tval const&);
        static tval tBinop(IROp, tval const&, tval const&);
        static tval tTriop(IROp, tval const&, tval const&, tval const&);
        static tval tQop(IROp, tval const&, tval const&, tval const&, tval const&);

        inline operator const z3::context& () const { return m_ctx; }
        inline operator const z3::vcontext& () const { return m_ctx; }
        inline operator const Z3_context() const { return m_ctx; }
        inline z3::vcontext& ctx() { return m_ctx; }
        inline const TR::vex_info& info() const { return m_vex_info; }
        
        virtual MEM_BASE& membase() {};
        //inline operator TR::State<Addr32>& () { return *reinterpret_cast <TR::State<Addr32>*>(this); };
        //inline operator TR::State<Addr64>& () { return *reinterpret_cast <TR::State<Addr64>*>(this); };
        //inline operator TR::State<Addr32>* () { return reinterpret_cast <TR::State<Addr32>*>(this); };
        //inline operator TR::State<Addr64>* () { return reinterpret_cast <TR::State<Addr64>*>(this); };
        ////必须存在至少一个virtual喔，不然上面4句转换就会产生错位
        //virtual Addr64 get_cpu_ip() { return 0; };

    private:


    };




    template<typename HWord>
    inline bool operator==(InvocationStack<HWord> const& a, InvocationStack<HWord> const& b) {
        return (a.guest_call_stack == b.guest_call_stack) && (a.guest_stack == b.guest_stack);
    }

};

#endif

