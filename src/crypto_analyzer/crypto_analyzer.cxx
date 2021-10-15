
#include "instopt/engine/tr_kernel.h"
#include "instopt/crypto_analyzer/crypto_analyzer.h"
#include "instopt/crypto_analyzer/analyzer.h"
#include "instopt/crypto_analyzer/ana_des.h"
using namespace z3;



const finder ana[] = {
    des_check_ro0,
    des_check_ro1,
    des_check_ro2,
    des_check_ro3
};

class ana_finder {
    std::deque<finder> m_ana;
    TR::StateBase& m_state;
    HWord m_base;
    expr m_idx;
    ana_decl m_ana_decl;
public:
    ana_finder(TR::StateBase& s, HWord base, Z3_ast index):
        m_state(s), m_base(base), m_idx(expr(s, index)), m_ana_decl(nullptr)
    {}

    bool check() {
        std::list<finder> fs;
        fs.assign(ana, &ana[sizeof(ana) / sizeof(void*)]);
        /*for (UInt n = 0; n < sizeof(ana) / sizeof(void*); n++) {
            fs[n] = ana[n];
        }*/

        static HASH_MAP<HWord, ana_decl> m_ana_decl_all;
        HASH_MAP<HWord, ana_decl>::iterator fa = m_ana_decl_all.find(m_base);
        if (fa != m_ana_decl_all.end()) {
            m_ana_decl = fa->second;
            return true;
        }

        UInt idx = 0;
        TR::Mem& mem = m_state.mem;
        while (fs.size()) {
            std::list<finder>::iterator itor = fs.begin();
            for (; itor != fs.end(); itor++) {
                finder f = *itor;
                auto value = mem.template load<Ity_I32>(m_base + (idx << 2));
                if (value.symb()) return false;
                ana_decl ad = f(idx, value.tor());
                if (!ad) {
                    itor = fs.erase(itor);
                    if (itor == fs.end()) break;
                }
                else {
                    if (ad == (ana_decl)-1) {
                        m_ana_decl_all[m_base] = m_ana_decl;
                        return true;
                    }
                    m_ana_decl = ad;
                }
            }
            idx++;
        }
        return false;
    }
    expr get() { return m_ana_decl(m_idx); }
    ana_decl get_method() { return m_ana_decl; }
};



expr crypto_finder(TR::StateBase& s, HWord base, Z3_ast index)
{
    ana_finder f(s, base, index);
    if (f.check()) {
        return f.get();
    }
    return expr(s);
}
