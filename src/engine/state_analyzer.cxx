/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    State analyzer.class:
Abstract:
    API list;
Author:
    WXC 2019-05-31.
Revision History:
--*/

#include "engine/state_analyzer.h"
#include <set>    
#include <map>   
#include <forward_list>

#ifdef _DEBUG
//#define OUTPUT
//#define OUTPUT_PATH
#endif

using namespace TR;

template<typename THword>
class StateAnalyzer {
    State<THword>& m_state;
public:
    StateAnalyzer(State<THword>& state) :
        m_state(state)
    {
    }


    void Run();

};

template<typename THword>
bool check_has_loop(State<THword>*s, THword oep) {
    while (s) {
        if (s->get_state_ep() == oep) {
            return true;
        }
        //s = s->m_father_state;
    }
    return false;
}

template<typename THword>
void find_explore_state(State<THword> &state, std::vector<State<THword>*>& explore, HASH_MAP<THword, UInt> &Fork_addr) {
   if (state.branch.empty()) {
        if (state.status() == Fork) {
            auto _where = Fork_addr.find(state.get_cpu_ip());
            if (_where == Fork_addr.end()) {
                for (State<THword>* nstate : state.branch) {
                    explore.emplace_back(nstate);
                }
            }
            else {
                Fork_addr[state.get_cpu_ip()] += 1;
            }
        }else if (state.status() == NewState) {
            explore.emplace_back(&state);
        }
        return;
   }
   else {
       for (State<THword>* cs : state.branch) {
           find_explore_state(*cs, explore, Fork_addr);
       }
   }
}


template<typename THword>
void find_fork_state(State<THword>& state, HASH_MAP<THword, UInt>& Fork_addr) {
    if (!state.branch.empty()) {
        Fork_addr[state.get_cpu_ip()] = 0;
        for (State<THword>* cs : state.branch) {
            find_fork_state(*cs, Fork_addr);
        }
    }
}

template<typename THword>
bool task_explorer(State<THword>* top) {
    vex_context<THword>& vctx = top->vctx();
    while (true) {
        HASH_MAP<THword, UInt> Fork_addr;
        std::vector<State<THword>*> explore;
        find_fork_state(*top, Fork_addr);
        find_explore_state(*top, explore, Fork_addr);

        if (!explore.empty()) {
            std::cout << *top << std::endl;
            for (State<THword>* nstate : explore) {
                vctx.pool().enqueue([nstate] {
                    nstate->start();
                    });
            }
            vctx.pool().wait();
            std::cout << *top << std::endl;
        }
        else {
            if(Fork_addr.empty())
                return false;
            std::cout << *top << std::endl;
            for (auto SD : Fork_addr) {
                printf("%p  %d ", (void*)(size_t)SD.first, SD.second);
                if (SD.second) {
                    std::vector<State_Tag> avoid;
                    avoid.emplace_back(Death);
                    //top->compress(SD.first, Fork, avoid);
                    std::cout << *top << std::endl;
                }
            }
        }
    };

    return false;

    //std::vector<State<THword>*> ForkTree;
    //ForkTree.emplace_back(top);
    //HASH_MAP<THword, UInt> Fork_addr;
    //HASH_MAP<THword, UInt> CompStates;
    //while (true)
    //{
    //    printf("++++2++++ {\n");
    //    bool has_task = False;
    //    for (State* s : ForkTree) {
    //        for (BranchChunk& bc : s->branchChunks) {
    //            auto _where = Fork_addr.lower_bound(bc.m_oep);
    //            if (_where == Fork_addr.end()) {
    //                s->branch.emplace_back(s->mkChildState(bc));
    //                has_task = True;
    //            }
    //            Fork_addr[bc.m_oep] = 0;
    //        }
    //    }

    //    for (State<THword>* s : ForkTree) {
    //        s->branchGo();
    //    }
    //    State<THword>::pool->wait();
    //    std::cout << *top << std::endl;
    //    printf("}----2-----\n");


    //    std::vector<State*> _ForkTree;
    //    for (State* bs : ForkTree) {
    //        if (!bs->branch.size()) {
    //            if (bs->status != Fork) continue;
    //            THword end_addr = bs->get_cpu_ip();
    //            CompStates[end_addr] = 1;
    //        }
    //        for (State* s : bs->branch) {
    //            _ForkTree.emplace_back(s);
    //        }
    //    }
    //    ForkTree.clear();
    //    ForkTree = _ForkTree;
    //    bool ret = false;
    //    if (!has_task) {
    //        std::cout << *top << std::endl;
    //        for (auto SD : CompStates) {
    //            printf("%p  %d ", SD.first, SD.second);
    //            if (SD.second) {
    //                std::vector<State_Tag> avoid;
    //                avoid.emplace_back(Death);
    //                top->compress(SD.first, Fork, avoid);
    //                ret = true;
    //            }
    //        }
    //        return ret;
    //    }
    //};
    //return false;
}

template<typename THword>
void StateAnalyzer<THword>::Run() {

    while (task_explorer(&m_state)) {
        std::cout << m_state << std::endl;
    };
}


template<typename THword, class _jmps = std::forward_list<THword>>
class GraphView {
    template<typename Ta> friend class PathExplorer;
    vex_info& m_info;
    MEM<THword>& m_mem;
    spin_mutex translate_mutex;
    typedef struct blockEnd {
        IRJumpKind kd;
        THword addr;
    };
    typedef enum { Loop_INVALID, Loop_True, Loop_False } loop_kind;
    typedef struct jmp_info {
        THword addr;
        loop_kind loop;
    };
public:
    using jmps = _jmps;
    using jmp_kind = std::forward_list<jmp_info>;
private:
    std::map<THword, jmp_kind> m_jmp;
    std::map<THword, _jmps> m_in;
    std::map<THword, THword> m_block_begin;
    std::map<THword, blockEnd> m_block_end;
    ThreadPool m_pool;
    
    inline THword tIRExpr(IRExpr* e, EmuEnvironment& ir_temp)
    {
        switch (e->tag) {
        case Iex_RdTmp: { return ir_temp[e->Iex.RdTmp.tmp]; }
        case Iex_Const: { return (THword)e->Iex.Const.con->Ico.U64; }
        case Iex_Load: {
            THword addr = tIRExpr(e->Iex.Load.addr, ir_temp);
            if (!addr) return 0;
            try {
                tval v = m_mem.Iex_Load(addr, e->Iex.Get.ty);
                if (v.symb()) return 0;
                return v;
            }
            catch (Expt::ExceptionBase & error) {
                std::cout << error << std::endl;
                return 0;
            }
        }
        };
        return 0;
    }

    void _add_block(THword block_start) {
        EmuEnvironment emu(info(), m_mem, info().gguest());
        THword     block_task = 0;
        THword guest_start = block_start;
        bool fresh = false; 
        for (;;) {
            if (getEnd(guest_start)) {
                goto End;
            }
            else
            {
                //m_mem.set_double_page(guest_start, emu);
                //emu.set_guest_bytes_addr(emu->t_page_addr, guest_start);
                VexRegisterUpdates pxControl;
                VexTranslateResult res;
                IRSB* irsb = LibVEX_FrontEnd(emu.get_ir_vex_translate_args(), &res, &pxControl);

                IRStmt* s = irsb->stmts[0];
                UInt code_len = 0;
                for (UInt stmtn = 0; stmtn < irsb->stmts_used;
                    s = irsb->stmts[++stmtn])
                {
                    //ppIRStmt(s);
                    //printf("\n");
                    switch (s->tag) {
                    case Ist_WrTmp: { emu[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data, emu); break; };
                    case Ist_Exit: {
                        if (s->Ist.Exit.jk != Ijk_SigSEGV) {
                            add_block(block_start, guest_start, s->Ist.Exit.jk, emu.get_ir_vex_translate_args());
                            _jmp_to(guest_start, s->Ist.Exit.dst->Ico.U64);
                            explore_block(block_task, s->Ist.Exit.dst->Ico.U64);
                            fresh = true;
                        }
                        break;
                    }
                    case Ist_AbiHint: {
                        THword call_start = tIRExpr(s->Ist.AbiHint.nia, emu);
                        if (call_start) {
                            explore_block(block_task, call_start);
                            _jmp_to(guest_start, call_start);
                            explore_block(block_task, guest_start + code_len);
                        }
                        // m_InvokStack.push(tIRExpr(s->Ist.AbiHint.nia), tIRExpr(s->Ist.AbiHint.base));
                        break;
                    }

                    case Ist_IMark: {
                        if (fresh) {
                            fresh = false;
                            _jmp_to(guest_start, s->Ist.IMark.addr);
                            block_start = s->Ist.IMark.addr;
                        }
                        guest_start = s->Ist.IMark.addr;
                        code_len = s->Ist.IMark.len;
                        break;
                    }
                    };


                }


                THword next = tIRExpr(irsb->next, emu);
                if (fresh) {
                    fresh = false;
                }
                else {
                    add_block(block_start, guest_start, irsb->jumpkind, emu.get_ir_vex_translate_args());
                }

                if (next) {
                    switch (irsb->jumpkind) {
                    case Ijk_Sys_syscall:
                    case Ijk_Boring:
                    {
                        _jmp_to(guest_start, next);
                        guest_start = next;
                        block_start = next;
                        break;
                    }
                    case Ijk_Call:goto End;
                    default:
                        //#ifdef OUTPUT
                        ppIRJumpKind(irsb->jumpkind);
                        printf("%p \n", guest_start);
                        //#endif
                        goto End;
                    };

                }
                else {
                    goto End;
                }
                continue;
            };
        End:
            if (block_task) {
                guest_start = block_task;
                block_start = block_task;
                fresh = false;
                block_task = 0;
                if (getEnd(guest_start)) {
                    return;
                }
            }
            else {
                return;
            }
        }



    }

    THword prev_code_addr(THword addr, THword this_code, VexTranslateArgs* vta) {
        //vexSetAllocModeTEMP_and_save_curr();
        /*
        m_mem.set_double_page(addr, pap);
        pap.mem_obj = (void*)&m_mem;
        pap.n_page_mem = EmuEnvironment::mem_next_page<THword>;
        pap.start_swap = 0;
        pap.guest_max_insns = m_info.gmax_insns();*/
        //vta->guest_bytes = pap.t_page_addr;
        vta->guest_bytes_addr = addr;
        VexRegisterUpdates pxControl;
        VexTranslateResult res;
        IRSB* irsb = LibVEX_FrontEnd(vta, &res, &pxControl);
        IRStmt* s = irsb->stmts[0];
        for (UInt stmtn = 0; stmtn < irsb->stmts_used;
            s = irsb->stmts[++stmtn])
        {                                                                                                                                                
            if (s->tag == Ist_IMark && s->Ist.IMark.addr + s->Ist.IMark.len >= this_code) {
                return s->Ist.IMark.addr;
            }
        }   
        return 0;
    }

    void add_block(THword block_start, THword block_end, IRJumpKind kd, VexTranslateArgs* vta) {
        if (kd == Ijk_SigSEGV) return;
        spin_unique_lock lock(translate_mutex);
        std::map<THword, blockEnd>::iterator it = m_block_end.find(block_end);
        /*if (0x00007ffff7a8d33d == block_start||0x00007ffff7a8d34a == block_start) {
            printf("");
        }*/
        if (it != m_block_end.end()) { 
            if (block_start > it->second.addr) {
                THword nEnd = prev_code_addr(it->second.addr, block_start, vta);
                m_block_begin[it->second.addr] = nEnd;
                //m_block_begin.insert(std::make_pair(it->second.addr, nEnd));
                _jmp_to_no_mutex(nEnd, block_start);
                m_block_end[nEnd] = blockEnd{ Ijk_Boring, it->second.addr };
                m_block_begin[block_start] = block_end;
#ifdef OUTPUT
                printf("update block %p   %p \n", it->second.addr, nEnd);
#endif
                it->second.addr = block_start;
            }
            else if(block_start < it->second.addr){
                block_end = prev_code_addr(block_start, it->second.addr, vta);
                kd = Ijk_Boring;
                if (!block_end) {
                    vassert(0);
                }
                _jmp_to_no_mutex(block_end, it->second.addr);
                vassert(block_start <= block_end);
                vassert(block_end < it->second.addr);
                goto NewBlock;
            }
        }
        else {
        NewBlock:
            m_block_end[block_end] = blockEnd{ kd, block_start };
            m_block_begin[block_start] = block_end;
#ifdef OUTPUT
            printf("new block %p   %p \n", block_start, block_end);
#endif
        }

    }

    void explore_block(THword& block_task, THword block_start) {
        if (block_task) {
            enqueue(block_start);
        }
        else {
            block_task = block_start;
        }
    }

    void enqueue(THword block_start) {
        if(!getEnd(block_start))
            m_pool.enqueue(
                [this, block_start] {
                    _add_block(block_start);
                }
            );
    }

    void _jmp_to(THword from, THword to) {
        spin_unique_lock lock(translate_mutex);
        _jmp_to_no_mutex(from, to);
    }

    inline  void _jmp_to_no_mutex(THword from, THword to) {
        if (from == 0) {
            vassert(0);
        }
#ifdef OUTPUT
        printf("_jmp_to %p   %p \n", from, to);
#endif
        std::map<THword, jmp_kind>::iterator it = m_jmp.find(from);
        if (it == m_jmp.end()) {
            m_jmp[from] = jmp_kind{ jmp_info{to, Loop_INVALID } };
        }
        else {
            it->second.push_front(jmp_info{ to, Loop_INVALID });
        }

        std::map<THword, _jmps>::iterator it_in = m_in.find(to);
        if (it_in == m_in.end()) {
            m_in[to] = _jmps{ from };
        }
        else {
            it_in->second.push_front(from);
        }
    }

    THword getBegin(THword block_end) {
        std::map<THword, blockEnd>::iterator it = m_block_end.find(block_end);
        if (it == m_block_end.end()) { return 0; }
        return it->second.addr;
    }

    THword getEnd(THword block_begin) {
        std::map<THword, THword>::iterator it = m_block_begin.find(block_begin);
        if (it == m_block_begin.end()) { return 0; }
        return it->second;
    }


public:
    GraphView(vex_info const& info, MEM<THword>& mem, THword oep) :m_pool(8), m_info(const_cast<vex_info&>(info)), m_mem(mem) {
        enqueue(oep);
    }
    inline const vex_info& info() const { return m_info; }
    void wait() { m_pool.wait(); }

    void explore_block(THword block_start) {
        std::map<THword, THword>::iterator it = m_block_begin.find(block_start);
        if (it != m_block_begin.end()) return;
        enqueue(block_start);
    }

    void add_jmp(THword from, THword to) {
        _jmp_to(from, to);
        explore_block(to);
    }



    THword begin2End(THword block_begin) {
        typename std::map<THword, THword>::iterator ait = m_block_begin.find(block_begin);
        if (ait == m_block_begin.end()) {
            if (0x00007ffff7a8d34a == block_begin) {
                printf("");
            }
            m_pool.enqueue(
                [this, block_begin] {
                    _add_block(block_begin);
                }
            );
            wait();
        }
        typename std::map<THword, THword>::iterator it = m_block_begin.find(block_begin);
        if (it == m_block_begin.end()) {
            return 0;
        }
        return it->second;
    }

};

template<typename THword>
class PathExplorer : public GraphView<THword> {

    template <class _Ty, class _Container = std::deque<_Ty>, class _jmps = std::forward_list<_Ty>>
    class Stack :protected _Container {
    public:
        typedef typename _Container::iterator iterator;
        using jmps = _jmps;
    private:
        HASH_MAP<_Ty, _jmps> m_stack_map;
    public:
        void pop() {
            _Container::reference v = _Container::back();
            m_stack_map.erase(m_stack_map.find(v));
            _Container::pop_back();
        }

        void push(const typename _Container::value_type && v) {
            m_stack_map[v] = _jmps{};
            _Container::push_back(v);
        }

        void push(const typename _Container::value_type& v) {
            m_stack_map[v] = _jmps{};
            _Container::push_back(v);
        }

        typename _Container::reference top() { return _Container::back(); }

        bool contains(_Ty v) {
            return m_stack_map.find(v) != m_stack_map.end();
        }

        bool empty() { return _Container::empty(); }

        void setVisited(_Ty from, _Ty end) {
            m_stack_map.find(from)->second.push_front(end);
        }

        jmps& getVertex(_Ty from) {
            return m_stack_map.find(from)->second;
        }

        jmps& getVertex() {
            return m_stack_map.find(top())->second;
        }

        iterator begin() { return  _Container::begin(); }
        iterator end() { return  _Container::end(); }
        iterator back() { return --_Container::end(); }
        UInt size() const { return _Container::size(); }
    };

public:
    PathExplorer(vex_info const& info, MEM<THword>& mem, THword oep) :GraphView<THword>(info, mem, oep) {
        
    }

    void set_visited(Int _itor, Stack<THword>& stack, HASH_MAP<THword, bool>& target) {
        typename Stack<THword>::iterator itor = stack.begin() + _itor;
#ifdef OUTPUT_PATH
        std::cout << *itor << " -> ";
#endif
        vassert(_itor + 1 < stack.size());
        target[*itor] = true;
        for (;;) {
            THword end = GraphView<THword>::getEnd(*itor++);
            if (itor == stack.end()) {
                break;
            }
            UInt dealt = 0;
            if (m_block_end[end].kd == Ijk_Call) {
                dealt = 5;
            }
            std::map<THword, GraphView<THword>::jmp_kind>::iterator to = m_jmp.find(end);
            typename GraphView<THword>::jmp_kind& vertexs = to->second;
            typename GraphView<THword>::jmp_kind::iterator  next = vertexs.begin();
            while (next != vertexs.end()) {
                THword addr = dealt ? (end + dealt) : next->addr;
                if (addr == *itor) {
#ifdef OUTPUT_PATH
                    std::cout << addr << " -> ";
#endif
                    next->loop = Loop_False;
                    target[addr] = true;
                    break;
                }
                next++;
            }
        };
#ifdef OUTPUT_PATH
        std::cout << std::endl;
#endif
    }

    THword getUnvisitedVertex(Stack<THword>& stack, THword vertex, HASH_MAP<THword, bool>& avoid) {
        THword block_end = begin2End(vertex);
        std::map<THword, GraphView<THword>::jmp_kind>::iterator to = m_jmp.find(block_end);
        if (to == m_jmp.end()) {
            return 0;
        }
        UInt dealt = 0;
        if (m_block_end[block_end].kd == Ijk_Call) {
            dealt = 5;
        }
       typename GraphView<THword>::jmp_kind& vertexs = to->second;
       typename GraphView<THword>::jmp_kind::iterator  next = vertexs.begin();
        while (next != vertexs.end()) {
            THword addr = dealt ? (block_end + dealt) : next->addr;
            typename Stack<THword>::jmps& vl = stack.getVertex();

            if (avoid.find(addr) == avoid.end()) {
                if (!stack.contains(addr)) {
                    if (std::find(vl.begin(), vl.end(), addr) == vl.end()) {
                        vl.push_front(addr);
                        return addr;
                    }
                }
            }

            next++;
        }
        return 0;
    }


    void get_path(THword start, THword end = 0) {
        Stack<THword> stack;
        HASH_MAP<THword, bool> block_target;
        HASH_MAP<THword, bool> avoid;
        stack.push(start);
        UInt prev_itor = 0;
        while (!stack.empty()) {
            THword TOP = stack.top();
            if (0x0007FFFF7A8D33D == TOP) {
                printf("");
            }
            THword next = getUnvisitedVertex(stack, TOP, avoid);
            if (next) {
                if (block_target.find(next) == block_target.end()) {
                    stack.push(next);
                }
                else {
#ifdef OUTPUT_PATH
                    std::cout << "[" << next << "]  ";
#endif
                    stack.push(next);
                    set_visited(prev_itor, stack, block_target);
                    stack.pop();
                    stack.pop();
                    prev_itor = stack.size() - 1;
                }
            }
            else {
                if (block_target.find(TOP) == block_target.end()) {
                    avoid[TOP] = true;
                }
                stack.pop();
                prev_itor = stack.size() - 1;
            }
            if (!stack.empty() && end == stack.top()) {
                set_visited(prev_itor, stack, block_target);
                stack.pop();
                prev_itor = stack.size() - 1;
            }
        }

    }



};


void test(State<Addr64>& m_state) {
    StateAnalyzer<Addr64> gv(m_state);
    gv.Run();

    TESTCODE(
        PathExplorer<Addr64> SS(m_state.info(), m_state.mem, m_state.get_cpu_ip());
    SS.wait();
    SS.get_path(0x07FFFF7A8CD50, 0x07FFFF7A8CEA3);
    );

    
}



template void StateAnalyzer<Addr32>::Run();
template void StateAnalyzer<Addr64>::Run();