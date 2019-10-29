#include "State_class.hpp"



class Block {
    ADDR m_front;
    ADDR m_end;
    std::vector<Block*> m_out;
    std::vector<Block*> m_in;
public:
    Block(ADDR front, ADDR end) :
        m_front(m_front),
        m_end(end)
    {

    }

    inline void push_in(Block& in) { m_in.emplace_back(&in); }
    inline void push_out(Block& out) { m_out.emplace_back(&out); }

private:

};

class GraphView :private State{
public:
    void analyze(Bool first_bkp_pass);
};



class StateAnalyzer {
    State& m_state;
public:
    StateAnalyzer(State& state) :
        m_state(state)
    {
    }

    void analyze(State *s, Bool first_bkp_pass) {
        ((GraphView*)s)->analyze(first_bkp_pass);
    }

    void Run();

};