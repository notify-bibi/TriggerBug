
//  分支合并的压缩算法 


#ifndef _STATE_COMPRESS_
#define _STATE_COMPRESS_
#include "engine/state_class.h"

Z3_context& thread_get_z3_ctx();


namespace cmpr {
    struct ignore {};

    static Vns logic_and(std::vector<Vns> const& v) {
        Z3_context ctx = v[0];
        UInt size = v.size();
        vassert(size > 0);
        if (size == 1) return v[0];
        Z3_ast* list = new Z3_ast[size];
        Z3_ast* ptr = list;
        for (Vns const& ass : v) { *ptr++ = ass; }
        return Vns(ctx, Z3_mk_and(ctx, size, list), 1);
    }

    static Vns logic_or(std::vector<Vns> const& v) {
        Z3_context ctx = v[0];
        UInt size = v.size();
        vassert(size > 0);
        if (size == 1) return v[0];
        Z3_ast* list = new Z3_ast[size];
        Z3_ast* ptr = list;
        for (Vns const& ass : v) { *ptr++ = ass; }
        return Vns(ctx, Z3_mk_or(ctx, size, list), 1);
    }

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

        Vns vec2ast(struct _m_vec_* v) const {
            return v->is_ast ? Vns(m_ctx, v->value.ast, 64) : Vns(m_ctx, v->value.data);
        }

        Vns _get(struct _m_vec_* vec) const {
            vassert(vec->m_maps_ass_idx > 0);
            Vns guard = Vns(m_ctx, vec->m_maps_ass_idx == 1 ? vec->m_maps_ass[0] : Z3_mk_or(m_ctx, vec->m_maps_ass_idx, vec->m_maps_ass), 1);

            return vec->sort ? ite(guard, vec2ast(vec), _get(vec->sort)) : vec2ast(vec);
        }

        void check() {
            if (m_idx >= m_size) {
                vassert(m_idx == m_size);
                UInt new_size = m_size * 2;
                m_vec = (_m_vec_*)realloc(m_vec, sizeof(_m_vec_) * new_size);
                for (struct _m_vec_* vec = m_sort; vec; vec = vec->sort) {
                    if (vec->m_maps_ass)
                        vec->m_maps_ass = (Z3_ast*)realloc(vec->m_maps_ass, new_size * sizeof(Z3_ast));
                }
                m_size = new_size;
            }
        }
    public:

        GPMana() :GPMana(thread_get_z3_ctx(), 16) {  };

        GPMana(Z3_context ctx, UInt size) :m_size(size), m_ctx(ctx), m_sort(nullptr) {
            m_vec = (_m_vec_*)malloc(sizeof(_m_vec_) * size);
            memset(m_vec, 0, sizeof(_m_vec_) * m_size);
        }

        GPMana(const GPMana& gp) :GPMana(gp.m_ctx, gp.m_size) {
            m_sort = m_vec;
            m_idx = gp.m_idx;
            UInt idx = 0;
            struct _m_vec_* this_vec = nullptr;
            for (struct _m_vec_* vec = gp.m_sort; vec; vec = vec->sort, idx++) {
                this_vec = &m_vec[idx];
                if (vec->m_maps_ass_idx) {
                    if (!this_vec->m_maps_ass) { this_vec->m_maps_ass = new Z3_ast[m_size]; }
                    for (UInt i = 0; i < vec->m_maps_ass_idx; i++) {
                        this_vec->m_maps_ass[i] = vec->m_maps_ass[i];
                        Z3_inc_ref(m_ctx, vec->m_maps_ass[i]);
                    }
                }
                this_vec->sort = &m_vec[idx + 1];
                this_vec->is_ast = vec->is_ast;
                this_vec->m_maps_ass_idx = vec->m_maps_ass_idx;
                if (this_vec->is_ast) {
                    this_vec->value.ast = vec->value.ast;
                    Z3_inc_ref(m_ctx, this_vec->value.ast);
                }
                else {
                    this_vec->value.data = vec->value.data;
                }
            }
            if (this_vec) {
                this_vec->sort = nullptr;
            }
            else {
                m_sort = nullptr;
            }
        }

        void operator=(const GPMana& gp)
        {
            this->~GPMana();
            this->GPMana::GPMana(gp);
        }


        void add(Vns const& ass, Vns const& v) {
            if (v.real()) add((Z3_ast)ass, (ULong)v); else  add((Z3_ast)ass, (Z3_ast)v);
        }

        void add(Z3_ast ass, Z3_ast v) {
            check();
            bool find = false;
            struct _m_vec_* vec = m_sort;
            struct _m_vec_* prv = nullptr;
            for (; vec; prv = vec, vec = vec->sort) {
                if (vec->is_ast && vec->value.ast == v) {
                    find = true;
                    break;
                }
            }
            if (!vec) {
                vec = &m_vec[m_idx++];
            }
            if (!find) {
                vec->is_ast = true;
                vec->value.ast = v;
                Z3_inc_ref(m_ctx, v);
                struct _m_vec_* next = m_sort;
                vec->sort = next;
                m_sort = vec;
            }
            if (!vec->m_maps_ass) { vec->m_maps_ass = (Z3_ast*)malloc(sizeof(Z3_ast) * m_size); };
            vec->m_maps_ass[vec->m_maps_ass_idx++] = ass;
            Z3_inc_ref(m_ctx, ass);
            if (find) mk_sort(prv, vec);
        }

        void add(Z3_ast ass, ULong v) {
            check();
            bool find = false;
            struct _m_vec_* vec = m_sort;
            struct _m_vec_* prv = nullptr;
            for (; vec; prv = vec, vec = vec->sort) {
                if (!vec->is_ast && vec->value.data == v) {
                    find = true;
                    break;
                }
            }
            if (!vec) {
                vec = &m_vec[m_idx++];
            }
            if (!find) {
                vec->value.data = v;
                vec->is_ast = false;
                struct _m_vec_* next = m_sort;
                vec->sort = next;
                m_sort = vec;
            }
            if (!vec->m_maps_ass) { vec->m_maps_ass = (Z3_ast*)malloc(sizeof(Z3_ast) * m_size); }
            vec->m_maps_ass[vec->m_maps_ass_idx++] = ass;
            Z3_inc_ref(m_ctx, ass);
            if (find) mk_sort(prv, vec);
        }

        void mk_sort(struct _m_vec_* prv, _m_vec_* new_vec) {
            //unlink
            if (new_vec->sort) {
                if (new_vec->m_maps_ass_idx > new_vec->sort->m_maps_ass_idx) {
                    if (prv) {
                        prv->sort = new_vec->sort;
                    }
                    else {
                        m_sort = new_vec->sort;
                    }
                }
                else {
                    return;
                }
            }
            //into
            struct _m_vec_* vec = prv ? prv->sort : m_sort;
            for (; vec; prv = vec, vec = vec->sort) {
                if (new_vec->m_maps_ass_idx <= vec->m_maps_ass_idx) {
                    prv->sort = new_vec;
                    new_vec->sort = vec;
                    return;
                }
            }
            prv->sort = new_vec;
            new_vec->sort = nullptr;
        }


        Vns get() const {
            vassert(m_idx > 0);
            return (m_idx == 1) ? vec2ast(m_sort) : _get(m_sort);
        }

        ~GPMana() {
            for (struct _m_vec_* vec = m_sort; vec; vec = vec->sort) {
                for (UInt idx = 0; idx < vec->m_maps_ass_idx; idx++) {
                    Z3_dec_ref(m_ctx, vec->m_maps_ass[idx]);
                }
                if (vec->is_ast) Z3_dec_ref(m_ctx, vec->value.ast);
                free(vec->m_maps_ass);
                vec->m_maps_ass = nullptr;
            }
            free(m_vec);
        }
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

        CmprsContext(const CmprsContext& ass) = delete;
        void operator =(const CmprsContext& ass) = delete;
    public:
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
        ~CmprsAvoid() override { del_obj(); }
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
        ~CmprsTarget() override { del_obj(); }
    };



    template<class STATEinterface /*= StateCmprsInterface<Addr64>*/>
    class CmprsFork :public STATEinterface {
        template<class STATEinterface, class CompressClass, typename StateStatus> friend class Compress;
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
            vassert(!branch().empty());
            m_child_nodes.reserve(branch().size());
            for (auto bstate : branch()) {
                STATEinterface* ns = mk(bstate, tag(bstate));
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

        inline STATEinterface& operator[](Int idx) { return child_nodes[idx]; }

        CmprsFork<STATEinterface>& get_fork_node() override { return *this; }

        ~CmprsFork() override {
            for (auto s : m_child_nodes) {
                delete s;
            };
            if (!has_survive()) del_obj();
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
                Vns m_assert;
                std::hash_map<Addr64, GPMana> m_changes;

                StateRes(Compress const& c, UInt group) :m_c(const_cast<Compress&>(c)), m_group(group),
                    m_assert(m_c.avoid_asserts(m_c.m_node, m_group))
                {
                    m_c.treeCompress(m_changes, m_c.m_node, m_group);
                }
            public:
                StateRes(const StateRes& ass) = delete;
                void operator =(const StateRes& ass) = delete;
                inline std::hash_map<Addr64, GPMana> const& changes() { return m_changes; }
                inline Vns conditions() const { return m_assert; }
            };
        public:

            Iterator(Compress const& c) :m_c(const_cast<Compress&>(c)), m_it_group(0) {
                m_group_max = m_c.m_ctx.group().size();
            }
            Iterator(const Iterator& ass) = delete;
            void operator =(const Iterator& ass) = delete;
            inline bool operator!=(const Iterator& src) { return m_it_group != src.m_group_max; }
            inline void operator++() { m_it_group++; }
            inline StateRes operator*() { return StateRes(m_c, m_it_group); }
            inline UInt group_max() { return m_group_max; }
        };
    private:
        Compress(const Compress& ass) = delete;
        void operator =(const Compress& ass) = delete;
    public:

        Compress(
            CmprsContext<CompressClass, StateStatus>& ctx,
            CompressClass& state
        ) :
            m_ctx(ctx), m_node(m_ctx, state, false)
        {

        }
        inline bool has_survive() { return m_node.has_survive(ignore{}); }
        inline operator z3::vcontext& () { return m_z3_target_ctx; }
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
        Vns avoid_asserts(CmprsFork<STATEinterface>& node, Int group) {
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
                    return Vns(m_ctx.ctx(), 0, 1);
                }
                std::vector<Vns> aasv;
                for (STATEinterface* sNode : node.child_nodes()) {
                    switch (sNode->type()) {
                    case Avoid_Node:
                    case Survive_Node: break;
                    case Fork_Node: {
                        if (sNode->get_fork_node().target_counts(group) == 0)
                            continue;
                        Vns aas_tmp = avoid_asserts(sNode->get_fork_node(), group);
                        Vns top = sNode->get_assert();
                        if (aas_tmp.real()) {
                            aasv.emplace_back(top);
                            continue;
                        }
                        aasv.emplace_back(implies(top, aas_tmp));
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
                    return Vns(m_ctx.ctx(), 0, 1);
                }
                std::vector<Vns> aasv;
                for (STATEinterface* sNode : node.child_nodes()) {
                    switch (sNode->type()) {
                    case Fork_Node: {
                        Vns top = sNode->get_assert();
                        if (sNode->get_fork_node().target_counts(group) == 0) {
                            aasv.emplace_back(top);
                            continue;
                        }
                        Vns aas_tmp = avoid_asserts(sNode->get_fork_node(), group);
                        if (aas_tmp.real()) {
                            continue;
                        }
                        aasv.emplace_back(implies(top, aas_tmp));
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
            std::hash_map<Addr64, Vns> m_cm;
            UInt m_size;
        public:
            __struct_cmaps__(STATEinterface* node, UInt size) :m_node(node), m_size(size) {
                m_cm.reserve(m_size);
            }

            void add(Addr64 addr, Vns const& m) {
                m_cm[addr] = m;
            }

            operator std::hash_map<Addr64, Vns>& () {
                return m_cm;
            }

            operator STATEinterface* () {
                return m_node;
            }

            bool exist(Addr64 a) {
                return m_cm.find(a) != m_cm.end();
            }

            void load(std::hash_map<Addr64, GPMana>& cm_ret, std::hash_map<Addr64, bool>& maps) {
                auto it_end = maps.end();
                auto it_start = maps.begin();
                Vns ass = m_node->get_assert();
                for (; it_start != it_end; it_start++) {
                    Addr64 addr = it_start->first;
                    if (exist(addr)) {
                        cm_ret[addr].add(ass, m_cm[addr]);
                    }
                    else {
                        Vns data = m_node->read(addr);
                        cm_ret[addr].add(ass, data);
                    }
                }
            }

            Vns& operator[](UInt idx) {
                return m_cm[idx];
            }

            ~__struct_cmaps__() { }
        };



        void treeCompress(
            std::hash_map<Addr64, GPMana>& cm_ret,/*OUT*/
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

            std::hash_map<Addr64, bool> record;
            for (__struct_cmaps__& changes_node : changes) {
                STATEinterface* sNode = changes_node;
                Vns top = sNode->get_assert();
                if (Fork_Node == sNode->type() && sNode->get_fork_node().target_counts(group)) {
                    sNode->get_write_map(record);
                    std::hash_map<Addr64, GPMana> cm_ret_tmp;
                    treeCompress(cm_ret_tmp, sNode->get_fork_node(), group);
                    auto it_end = cm_ret_tmp.end();
                    auto it_start = cm_ret_tmp.begin();
                    std::hash_map<Addr64, Vns>& fork_cm = changes_node;
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


    using Context32 = CmprsContext<TR::State<Addr32>, TR::State_Tag>;
    using Context64 = CmprsContext<TR::State<Addr64>, TR::State_Tag>;

};




#endif