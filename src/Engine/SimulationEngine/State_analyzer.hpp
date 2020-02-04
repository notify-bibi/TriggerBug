#include "State_class.hpp"



template<typename ADDR>
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


template<typename ADDR>
class StateAnalyzer {
    State<ADDR>& m_state;
public:
    StateAnalyzer(State<ADDR>& state) :
        m_state(state)
    {
    }


    void Run();

};
