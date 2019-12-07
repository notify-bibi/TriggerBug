#include "State_analyzer.hpp"



bool check_has_loop(State *s, ADDR oep) {
    while (s) {
        if (s->get_state_ep() == oep) {
            return true;
        }
        s = s->m_father_state;
    }
    return false;
}


bool task_explorer(State* top) {
    {
        printf("++++1++++\n");
        State* s = top;
        State::pool->enqueue([s] {
            s->start(True);
            });
        State::pool->wait();
        printf("----1-----\n");
    }
    std::vector<State*> ForkTree;
    ForkTree.emplace_back(top);
    std::hash_map<ADDR, UInt> Fork_addr;
    std::hash_map<ADDR, UInt> CompStates;
    while (true)
    {
        printf("++++2++++\n");
        bool has_task = False;
        for (State* s : ForkTree) {
            for (BranchChunk& bc : s->branchChunks) {
                auto _where = Fork_addr.lower_bound(bc.m_oep);
                if (_where == Fork_addr.end()) {
                    s->branch.emplace_back(bc.getState(*s));
                    has_task = True;
                }
                Fork_addr[bc.m_oep] = 0;
            }
        }

        for (State* s : ForkTree) {
            s->branchGo();
        }
        State::pool->wait();
        printf("----2-----\n");


        std::vector<State*> _ForkTree;
        for (State* bs : ForkTree) {
            if (!bs->branch.size()) {
                ADDR end_addr = bs->get_cpu_ip();
                auto _where = CompStates.lower_bound(end_addr);
                if (_where == CompStates.end()) {
                    CompStates[end_addr] = 0;
                }
                else {
                    CompStates[end_addr] = 1;
                }
            }
            for (State* s : bs->branch) {
                _ForkTree.emplace_back(s);
            }
        }
        ForkTree.clear();
        ForkTree = _ForkTree;
        bool ret = false;
        if (!has_task) {
            std::cout << *top << std::endl;
            for (auto SD : CompStates) {
                printf("%p  %d ", SD.first, SD.second);
                if (SD.second) {
                    std::vector<State_Tag> avoid;
                    avoid.emplace_back(Death);
                    top->compress(SD.first, Fork, avoid);
                    ret = true;
                }
            }
            return ret;
        }
    };
    return false;
}

void StateAnalyzer::Run() {
    while (task_explorer(&m_state)) {
        std::cout << m_state << std::endl;
    };
}


static UInt mk_key(Int offset, IRType ty)
{
    /* offset should fit in 16 bits. */
    UInt minoff = offset;
    UInt maxoff = minoff + sizeofIRType(ty) - 1;
    vassert((minoff & ~0xFFFF) == 0);
    vassert((maxoff & ~0xFFFF) == 0);
    return (minoff << 16) | maxoff;
}

IRExpr* Vns2Con(Vns const& v) {
    IRExpr* r = IRExpr_Const(IRConst_U64(v));
    r->Iex.Const.con->tag = v;
    return r;
}


void GraphView::run()
{

    State::pool->wait();



}
