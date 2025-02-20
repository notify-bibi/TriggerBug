
//  分支合并的压缩算法 


#ifndef _STATE_COMPRESS_
#define _STATE_COMPRESS_

#include "instopt/engine/engine.h"
#include "instopt/engine/basic_var.hpp"

Z3_context& thread_get_z3_ctx();

#define PACK rsval<uint64_t>


 sbool logic_and(std::vector<sbool> const& v);
 sbool logic_or(std::vector<sbool> const& v);

namespace cmpr {
    struct ignore {};


    class GPMana {
        Z3_context m_ctx;
        struct _m_vec_ {
            bool is_ast;
            union { Z3_ast ast; ULong data; } value;
            Z3_ast* m_maps_ass;
            UInt m_maps_ass_idx;
            struct _m_vec_* sort;
        }*m_vec;
        struct _m_vec_* m_sort;

        UInt m_idx = 0;
        UInt m_size;

        PACK vec2ast(struct _m_vec_* v) const;

        PACK _get(struct _m_vec_* vec) const;

        void check();
    public:

        GPMana() :GPMana(thread_get_z3_ctx(), 16) {  };

        GPMana(Z3_context ctx, UInt size);

        GPMana(const GPMana& gp);

        void operator=(const GPMana& gp);

        void debug_display();

        void add(sbool const& ass, PACK const& v);

        void add(Z3_ast ass, Z3_ast v);

        void add(Z3_ast ass, ULong v);

        void mk_sort(struct _m_vec_* prv, _m_vec_* new_vec);

        PACK get() const;

        ~GPMana();
    };

    typedef enum :Int {
        //子节点
        Fork_Node = -3,
        //叶子节点
        Avoid_Node,
        Survive_Node,
        //target node: 0-n
    }StateType;


    template<class CompressClass, typename StateStatus>
    class CmprsContext {
        Addr64 m_target_addr;
        StateStatus m_target_tag;
        std::vector<StateStatus> m_avoid;
        std::vector<CompressClass*> m_group;
        z3::vcontext& m_z3_target_ctx;

    public:
        CmprsContext(const CmprsContext& ass) { FAILD_ASSERT(CompressClass, "not support"); };
        void operator =(const CmprsContext& ass) { FAILD_ASSERT(CompressClass, "not support"); };

        CmprsContext(z3::vcontext& target_ctx, Addr64 target_addr, StateStatus ttag)
            :m_target_addr(target_addr), m_target_tag(ttag), m_z3_target_ctx(target_ctx)
        {
            thread_get_z3_ctx() = target_ctx;
        }
        void add_avoid(StateStatus avoid_tag) { m_avoid.emplace_back(avoid_tag); };
        bool is_avoid(StateStatus tag) { return std::find(m_avoid.begin(), m_avoid.end(), tag) != m_avoid.end(); }
        Addr64 get_target_addr() { return m_target_addr; }
        std::vector<CompressClass*>& group() { return m_group; }
        inline z3::vcontext& ctx() { return m_z3_target_ctx; }
        inline operator z3::vcontext& () { return m_z3_target_ctx; }
    };





    template<class STATEinterface>
    class CmprsFork;
    template<class STATEinterface>
    class CmprsTarget;



    template<class STATEinterface>
    class CmprsAvoid :public STATEinterface {
    public:
        template<class _CTX, class _S>
        CmprsAvoid(_CTX& ctx, _S& s) :STATEinterface(ctx, s, Avoid_Node) { }
        ~CmprsAvoid() override { this->del_obj(); }
    };



    template<class STATEinterface>
    class CmprsSurvive :public STATEinterface {
    public:
        template<class _CTX, class _S>
        CmprsSurvive(_CTX& ctx, _S& s) :STATEinterface(ctx, s, Survive_Node) { }
        ~CmprsSurvive() override { };
    };




    template<typename STATEinterface>
    class CmprsTarget :public STATEinterface {
        UInt m_group_id;

    public:
        template<class _CTX, class _S>
        CmprsTarget(_CTX& ctx, _S& s, Int ty) :STATEinterface(ctx, s, (StateType)ty) {
            vassert(ty >= 0);
        };
        CmprsTarget<STATEinterface>& get_target_node() override { return *this; }
        ~CmprsTarget() override { this->del_obj(); }
    };



    template<class STATEinterface /*= StateCmprsInterface*/>
    class CmprsFork :public STATEinterface {
        template<class _STATEinterface, class CompressClass, typename StateStatus> friend class Compress;
        StateType m_compr_ty;
        std::vector<STATEinterface*> m_child_nodes;
        bool m_has_survive = false;
        bool __m_has_survive__ = false;
        std::vector<Int> m_target_counts;
    public:
        template<class _CTX, class _S>
        CmprsFork(_CTX& ctx, _S& s, bool) :CmprsFork(ctx, s) { m_has_survive = true; }
        template<class _CTX, class _S>
        CmprsFork(_CTX& ctx, _S& s) : STATEinterface(ctx, s, Fork_Node) {
            vassert(!this->branch().empty());
            m_child_nodes.reserve(this->branch().size());
            for (auto _bstate : this->branch()) {
                State* bstate = (State*)_bstate;
                STATEinterface* ns = mk(bstate, this->tag(bstate));
                m_child_nodes.emplace_back(ns);
                if (ns->type() == Survive_Node) {
                    m_has_survive = true;
                }
                if (ns->type() == Fork_Node && ns->has_survive()) {
                    m_has_survive = true;
                }
                if (ns->type() == Fork_Node) {
                    UInt max = ns->get_fork_node().m_target_counts.size();
                    if (max >= m_target_counts.size()) {
                        for (Int g = m_target_counts.size(); g <= max; g++) {
                            m_target_counts.emplace_back(0);
                        }
                    }
                    for (UInt p = 0; p < max; p++) {
                        m_target_counts[p] += ns->get_fork_node().target_counts(p);
                    }
                }
                if (ns->type() >= 0) {
                    if (ns->type() >= m_target_counts.size()) {
                        for (Int p = m_target_counts.size(); p <= ns->type(); p++) {
                            m_target_counts.emplace_back(0);
                        }
                    }
                    m_target_counts[ns->type()] += 1;
                }
            }
            __m_has_survive__ = m_has_survive;
        }


        bool has_survive(struct ignore) { return __m_has_survive__; }

        bool has_survive() override { return m_has_survive; }

        UInt target_counts(UInt group) const {
            if (group >= m_target_counts.size()) {
                return 0;
            }
            return m_target_counts[group];
        }

        inline std::vector<STATEinterface*>& child_nodes() { return m_child_nodes; }

        inline STATEinterface& operator[](Int idx) { return m_child_nodes[idx]; }

        CmprsFork<STATEinterface>& get_fork_node() override { return *this; }

        ~CmprsFork() override {
            for (auto s : m_child_nodes) {
                delete s;
            };
            if (!has_survive()) this->del_obj();
        }
    };



    template<class STATEinterface, class CompressClass, typename StateStatus>
    class Compress {
        CmprsContext<CompressClass, StateStatus>& m_ctx;
        CmprsFork<STATEinterface> m_node;
    public:
        class Iterator {
            friend class Compress;
            Compress& m_c;
            UInt m_it_group;
            UInt m_group_max;

            //state compression results
        public:
            class StateRes {
                friend class Compress::Iterator;
                Compress& m_c;
                UInt m_group;
                sbool m_assert;
                HASH_MAP<Addr64, GPMana> m_changes;

                StateRes(Compress const& c, UInt group) :m_c(const_cast<Compress&>(c)), m_group(group),
                    m_assert(m_c.avoid_asserts(m_c.m_node, m_group).tos())
                {
                    m_c.treeCompress(m_changes, m_c.m_node, m_group);
                }
            public:
                StateRes(const StateRes& ass) { FAILD_ASSERT(STATEinterface, "not support"); };
                void operator =(const StateRes& ass) { FAILD_ASSERT(STATEinterface, "not support"); };
                inline HASH_MAP<Addr64, GPMana> const& changes() { return m_changes; }
                inline sbool conditions() const { return m_assert; }
            };
        public:

            Iterator(Compress const& c) :m_c(const_cast<Compress&>(c)), m_it_group(0) {
                m_group_max = m_c.m_ctx.group().size();
            }
            Iterator(const Iterator& ass) { FAILD_ASSERT(STATEinterface, "not support"); };
            void operator =(const Iterator& ass) { FAILD_ASSERT(STATEinterface, "not support"); };
            inline bool operator!=(const Iterator& src) { return m_it_group != src.m_group_max; }
            inline void operator++() { m_it_group++; }
            inline StateRes operator*() { return StateRes(m_c, m_it_group); }
            inline UInt group_max() { return m_group_max; }
        };
    private:
        Compress(const Compress& ass) { FAILD_ASSERT(STATEinterface, "not support"); };
        void operator =(const Compress& ass) { FAILD_ASSERT(STATEinterface, "not support"); };
    public:

        Compress(
            CmprsContext<CompressClass, StateStatus>& ctx,
            CompressClass& state
        ) :
            m_ctx(ctx), m_node(m_ctx, state, false)
        {

        }
        inline bool has_survive() { return m_node.has_survive(ignore{}); }
        inline operator z3::vcontext& () { return this->m_z3_target_ctx; }
        Iterator begin() const { return Iterator(*this); }
        Iterator end() const { return Iterator(*this); }
        void clear_nodes() {
            for (auto s : m_node.m_child_nodes) {
                delete s;
            };
            m_node.m_child_nodes.clear();
        }
        /*
        ┐(P∧Q)<=> ┐P∨┐Q
        ┐(P∨Q)<=> ┐P∧┐Q
        P∨(Q∧R)<=>(P∨Q)∧(P∨R)
        P∧(Q∨R)<=>(P∧Q)∨(P∧R)
        ┐(P→Q)<=> P∧┐Q
        P→Q<=>┐P∨Q
                               top
                               P1

                  A                           B
                  P2

            a1  a2  -a1 -a2              b-1  b0   b1
            Q1  Q2   q1  q2

        yes  P2 → (Q1 ∨ Q2) <=> ┐P2 ∨ (Q1 ∨ Q2) <=> ┐P2 ∨ Q1 ∨ Q2
        sat:  P2 Q1 Q2
              1  1  1
              1  0  1
              1  1  0
              0  x  x

        yes  P2 → (┐q1 ∧ ┐q2) <=> P2 → ┐(q1 ∨ q2) <=> ┐P2 ∨ (┐q1 ∧ ┐q2) <=> ┐P2 ∨ (┐q1 ∧ ┐q2)
        sat:  P2 q1 q2
              1  0  0
              0  x  x
        */
        rsbool avoid_asserts(CmprsFork<STATEinterface>& node, Int group) {
            UInt avoid_num = 0;
            UInt target_num = 0;
            for (STATEinterface* sNode : node.child_nodes()) {
                switch (sNode->type()) {
                case Avoid_Node:
                case Survive_Node: avoid_num += 1; break;
                case Fork_Node: {
                    if (sNode->get_fork_node().target_counts(group)) {
                        target_num += 1;
                    }
                    else {
                        avoid_num += 1;
                    }
                    break;
                }
                default: {
                    if ((StateType)group == sNode->type()) target_num += 1;
                }
                };
            }
            if (target_num <= avoid_num) {
                // P2 → (Q1 ∨ Q2)
                if (!target_num) {
                    return rsbool(m_ctx.ctx(), false);
                }
                std::vector<sbool> aasv;
                for (STATEinterface* sNode : node.child_nodes()) {
                    switch (sNode->type()) {
                    case Avoid_Node:
                    case Survive_Node: break;
                    case Fork_Node: {
                        if (sNode->get_fork_node().target_counts(group) == 0)
                            continue;
                        rsbool aas_tmp = avoid_asserts(sNode->get_fork_node(), group);
                        sbool top = sNode->get_assert();
                        if (aas_tmp.real()) {
                            aasv.emplace_back(top);
                            continue;
                        }
                        aasv.emplace_back(implies(top, aas_tmp.tos()));
                        break;
                    }
                    default: {
                        if ((StateType)group == sNode->type())
                            aasv.emplace_back(sNode->get_assert());
                    }
                    };
                }
                vassert(aasv.size() > 0);
                return logic_or(aasv);
            }
            else {
                // P2 → ┐(q1 ∨ q2)
                if (!avoid_num) {
                    return rsbool(m_ctx.ctx(), false);
                }
                std::vector<sbool> aasv;
                for (STATEinterface* sNode : node.child_nodes()) {
                    switch (sNode->type()) {
                    case Fork_Node: {
                        sbool top = sNode->get_assert();
                        if (sNode->get_fork_node().target_counts(group) == 0) {
                            aasv.emplace_back(top);
                            continue;
                        }
                        rsbool aas_tmp = avoid_asserts(sNode->get_fork_node(), group);
                        if (aas_tmp.real()) {
                            continue;
                        }
                        aasv.emplace_back(implies(top, aas_tmp.tos()));
                        break;
                    }
                    case Survive_Node:
                    case Avoid_Node: {
                        aasv.emplace_back(sNode->get_assert());
                        break;
                    }
                    default: {
                        if ((StateType)group != sNode->type())
                            aasv.emplace_back(sNode->get_assert());

                        break;
                    }
                    };
                }
                vassert(aasv.size() > 0);
                return !logic_or(aasv);
            }


        }

    private:

        class __struct_cmaps__ {
            STATEinterface* m_node;
            HASH_MAP<Addr64, PACK> m_cm;
            UInt m_size;
        public:
            __struct_cmaps__(STATEinterface* node, UInt size) :m_node(node), m_size(size) {
                m_cm.reserve(m_size);
            }

            void add(Addr64 addr, PACK const& m) {
                m_cm[addr] = m;
            }

            operator HASH_MAP<Addr64, PACK>& () {
                return m_cm;
            }

            operator STATEinterface* () {
                return m_node;
            }

            bool exist(Addr64 a) {
                return m_cm.find(a) != m_cm.end();
            }

            void load(HASH_MAP<Addr64, GPMana>& cm_ret, HASH_MAP<Addr64, bool>& maps) {
                auto it_end = maps.end();
                auto it_start = maps.begin();
                sbool ass = m_node->get_assert();
                for (; it_start != it_end; it_start++) {
                    Addr64 addr = it_start->first;
                    if (exist(addr)) {
                        cm_ret[addr].add(ass, m_cm[addr]);
                    }
                    else {
                        PACK data = m_node->read(addr);
                        cm_ret[addr].add(ass, data);
                    }
                }
            }

            PACK& operator[](UInt idx) {
                return m_cm[idx];
            }

            ~__struct_cmaps__() { }
        };



        void treeCompress(
            HASH_MAP<Addr64, GPMana>& cm_ret,/*OUT*/
            CmprsFork<STATEinterface>& node, Int group/*IN*/
        ) {
            std::vector<__struct_cmaps__> changes;
            UInt max = 0;
            for (STATEinterface* sNode : node.child_nodes()) {
                if (sNode->type() >= 0 || (Fork_Node == sNode->type() && sNode->get_fork_node().target_counts(group))) {
                    changes.emplace_back(__struct_cmaps__(sNode, 10));
                    max++;
                }
            }
            changes.reserve(max);

            HASH_MAP<Addr64, bool> record;
            for (__struct_cmaps__& changes_node : changes) {
                STATEinterface* sNode = changes_node;
                ///sbool top = sNode->get_assert();
                if (Fork_Node == sNode->type() && sNode->get_fork_node().target_counts(group)) {
                    sNode->get_write_map(record);
                    HASH_MAP<Addr64, GPMana> cm_ret_tmp;
                    treeCompress(cm_ret_tmp, sNode->get_fork_node(), group);
                    auto it_end = cm_ret_tmp.end();
                    auto it_start = cm_ret_tmp.begin();
                    HASH_MAP<Addr64, PACK>& fork_cm = changes_node;
                    for (; it_start != it_end; it_start++) {
                        changes_node.add(it_start->first, it_start->second.get());
                        record[it_start->first];
                    }
                }
                if ((StateType)group == sNode->type()) {
                    CmprsTarget<STATEinterface>& target = sNode->get_target_node();
                    sNode->get_write_map(record);
                }
            }

            for (__struct_cmaps__& changes_node : changes) {
                STATEinterface* sNode = changes_node;
                changes_node.load(cm_ret, record);
            }


        }

    };

};



#endif