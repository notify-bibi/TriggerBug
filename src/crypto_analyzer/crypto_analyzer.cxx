
#include "engine/tr_main.h"
#include "crypto_analyzer/crypto_analyzer.h"
#include "crypto_analyzer/analyzer.h"
#include "crypto_analyzer/ana_des.h"
using namespace z3;


class finder {
    std::deque<analyzer> m_ana;
    finder(const TR::State<Addr32>& s, Addr64 base, Z3_ast index) {

    }
    finder(const TR::State<Addr64>& s, Addr64 base, Z3_ast index) {

    }


};





expr crypto_finder32(const TR::State<Addr32>& s, Addr64 base, Z3_ast index)
{

    return expr(s);
}


expr crypto_finder64(const TR::State<Addr64>& s, Addr64 base, Z3_ast index)
{

    return expr(s);
}
