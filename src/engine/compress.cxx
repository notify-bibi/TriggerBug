#include "compress.h"

using namespace cmpr;

thread_local Z3_context thread_z3_ctx;
Z3_context& thread_get_z3_ctx() {
    return thread_z3_ctx; 
}

sbool logic_and(std::vector<sbool> const& v)
{
    if (v.size() == 0) {
        return sbool((Z3_context)(0));
    }
    else if (v.size() == 1) {
        return v[0];
    }
    Z3_context ctx = v[0];
    UInt size = v.size();
    vassert(size > 0);
    if (size == 1) return v[0];
    Z3_ast* list = new Z3_ast[size];
    Z3_ast* ptr = list;
    for (sbool const& ass : v) { *ptr++ = ass; }
    return sbool(ctx, Z3_mk_and(ctx, size, list));
}

sbool logic_or(std::vector<sbool> const& v)
{
    if (v.size() == 0) {
        return sbool((Z3_context)(0));
    }
    else if (v.size() == 1) {
        return v[0];
    }
    Z3_context ctx = v[0];
    UInt size = v.size();
    vassert(size > 0);
    if (size == 1) return v[0];
    Z3_ast* list = new Z3_ast[size];
    Z3_ast* ptr = list;
    for (sbool const& ass : v) { *ptr++ = ass; }
    return sbool(ctx, Z3_mk_or(ctx, size, list));
}

PACK cmpr::GPMana::vec2ast(_m_vec_* v) const
{
    return v->is_ast ? PACK(m_ctx, v->value.ast) : PACK(m_ctx, v->value.data);
}

PACK cmpr::GPMana::_get(_m_vec_* vec) const
{
    vassert(vec->m_maps_ass_idx > 0);
    sbool guard(m_ctx, vec->m_maps_ass_idx == 1 ? vec->m_maps_ass[0] : Z3_mk_or(m_ctx, vec->m_maps_ass_idx, vec->m_maps_ass));

    if (vec->sort) {
        return ite(guard, vec2ast(vec).tos(), _get(vec->sort).tos());
    }
    return vec2ast(vec);
}

void cmpr::GPMana::check()
{
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

cmpr::GPMana::GPMana(Z3_context ctx, UInt size)
    :m_size(size), m_ctx(ctx), m_sort(nullptr) {
    m_vec = (_m_vec_*)malloc(sizeof(_m_vec_) * size);
    memset(m_vec, 0, sizeof(_m_vec_) * m_size);
}

cmpr::GPMana::GPMana(const GPMana& gp)
    :GPMana(gp.m_ctx, gp.m_size) {
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

void cmpr::GPMana::operator=(const GPMana& gp)
{
    this->~GPMana();
    this->GPMana::GPMana(gp);
}

void cmpr::GPMana::add(sbool const& ass, PACK const& v)
{
    if (v.real()) add((Z3_ast)ass, (ULong)v.tor()); else  add((Z3_ast)ass, (Z3_ast)v.tos());
}

void cmpr::GPMana::debug_display() {
    struct _m_vec_* vec = m_sort;
    struct _m_vec_* prv = nullptr;
    for (; vec; prv = vec, vec = vec->sort) {
        std::cout << std::hex << vec->value.ast << "<" << vec->m_maps_ass_idx << ">, ";
    }
    std::cout << std::endl;
}


void cmpr::GPMana::add(Z3_ast ass, Z3_ast v)
{
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

void cmpr::GPMana::add(Z3_ast ass, ULong v)
{
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

void cmpr::GPMana::mk_sort(_m_vec_* prv, _m_vec_* new_vec)
{
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
    if (vec != new_vec) {
        for (; vec; prv = vec, vec = vec->sort) {
            if (new_vec->m_maps_ass_idx <= vec->m_maps_ass_idx) {
                prv->sort = new_vec;
                new_vec->sort = vec;
                return;
            }
        }
    }
    prv->sort = new_vec;
    new_vec->sort = nullptr;
}

PACK cmpr::GPMana::get() const
{
    vassert(m_idx > 0);
    return (m_idx == 1) ? vec2ast(m_sort) : _get(m_sort);
}

cmpr::GPMana::~GPMana()
{
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
