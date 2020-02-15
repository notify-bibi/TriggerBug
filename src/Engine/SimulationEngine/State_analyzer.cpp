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

#include "State_analyzer.hpp"
template<typename ADDR>
bool check_has_loop(State<ADDR>*s, ADDR oep) {
    while (s) {
        if (s->get_state_ep() == oep) {
            return true;
        }
        //s = s->m_father_state;
    }
    return false;
}

template<typename ADDR>
void find_explore_state(State<ADDR> &state, std::vector<State<ADDR>*>& explore, std::hash_map<ADDR, UInt> &Fork_addr) {
   if (state.branch.empty()) {
        if (state.status() == Fork) {
            auto _where = Fork_addr.lower_bound(state.get_cpu_ip());
            if (_where == Fork_addr.end()) {
                for (State<ADDR>* nstate : state.branch) {
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
       for (State<ADDR>* cs : state.branch) {
           find_explore_state(*cs, explore, Fork_addr);
       }
   }
}


template<typename ADDR>
void find_fork_state(State<ADDR>& state, std::hash_map<ADDR, UInt>& Fork_addr) {
    if (!state.branch.empty()) {
        Fork_addr[state.get_cpu_ip()] = 0;
        for (State<ADDR>* cs : state.branch) {
            find_fork_state(*cs, Fork_addr);
        }
    }
}

template<typename ADDR>
bool task_explorer(State<ADDR>* top) {

    while (true) {
        std::hash_map<ADDR, UInt> Fork_addr;
        std::vector<State<ADDR>*> explore;
        find_fork_state(*top, Fork_addr);
        find_explore_state(*top, explore, Fork_addr);

        if (!explore.empty()) {
            std::cout << *top << std::endl;
            for (State<ADDR>* nstate : explore) {
                Kernel::pool->enqueue([nstate] {
                    nstate->start(True);
                    });
            }
            Kernel::pool->wait();
            std::cout << *top << std::endl;
        }
        else {
            if(Fork_addr.empty())
                return false;
            std::cout << *top << std::endl;
            for (auto SD : Fork_addr) {
                printf("%p  %d ", SD.first, SD.second);
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

    //std::vector<State*> ForkTree;
    //ForkTree.emplace_back(top);
    //std::hash_map<ADDR, UInt> Fork_addr;
    //std::hash_map<ADDR, UInt> CompStates;
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

    //    for (State* s : ForkTree) {
    //        s->branchGo();
    //    }
    //    State::pool->wait();
    //    std::cout << *top << std::endl;
    //    printf("}----2-----\n");


    //    std::vector<State*> _ForkTree;
    //    for (State* bs : ForkTree) {
    //        if (!bs->branch.size()) {
    //            if (bs->status != Fork) continue;
    //            ADDR end_addr = bs->get_cpu_ip();
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

template<typename ADDR>
void StateAnalyzer<ADDR>::Run() {
    while (task_explorer(&m_state)) {
        std::cout << m_state << std::endl;
    };
}


template void StateAnalyzer<Addr32>::Run();
template void StateAnalyzer<Addr64>::Run();