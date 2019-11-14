#include "State_class.hpp"



class Block {
    ADDR m_front;
    ADDR m_end;
    std::vector<Block*> m_out;
    std::vector<Block*> m_in;
public:
    inline Block(ADDR front = 0, ADDR end = 0) :
        m_front(m_front),
        m_end(end){}
    inline void setfront(ADDR front) { m_front = front; }
    inline void setEnd(ADDR end) { m_end = end; }
    inline void push_in(Block& in) { m_in.emplace_back(&in); }
    inline void push_out(Block& out) { m_out.emplace_back(&out); }

private:

};

class GraphView{
    State& m_state;
    context& m_ctx;
    Register<REGISTER_LEN>& regs;
    MEM& mem;
    UShort t_index;
    ADDR guest_start_ep;
    ADDR guest_start;
    bool is_dynamic_block;
    Pap pap; 
    Long delta;
public:
    GraphView(State& state):
        m_state(state),
        m_ctx(state),
        regs(state.regs),
        mem(state.mem),
        t_index(0),
        guest_start_ep(state.guest_start_ep),
        guest_start(state.guest_start),
        pap(state.pap),
        delta(0)
    {
    }
    IRSB* BB2IR();
    inline Vns tIRExpr(IRExpr* e);
    void analyze(ADDR block_oep, Bool first_bkp_pass);
};



class StateAnalyzer {
    State& m_state;
public:
    StateAnalyzer(State& state) :
        m_state(state)
    {
    }

    void analyze(State &s, Bool first_bkp_pass) {
        GraphView gv(s);
        gv.analyze(s.get_start_of_block(), first_bkp_pass);
    }

    void Run();

};