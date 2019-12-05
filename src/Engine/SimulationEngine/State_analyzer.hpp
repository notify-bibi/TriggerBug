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




class IRT {
    UInt irTempSize;
    IRExpr** irTemp;
public:
    IRT() {
        irTempSize = 10;
        irTemp = (IRExpr**)malloc(sizeof(IRExpr*) * irTempSize);
    }

    IRExpr*& operator [](UInt idx) {
        if (idx >= irTempSize) {
            if (idx < 2 * irTempSize) {
                IRExpr** newtmp = (IRExpr**)malloc(sizeof(IRExpr*) * 2 * irTempSize);
                for (int i = 0; i < irTempSize; i++) {
                    newtmp[i] = irTemp[i];
                }
                irTempSize = 2 * irTempSize;
                irTemp = newtmp;
            }
            else {
                IRExpr** newtmp = (IRExpr**)malloc(sizeof(IRExpr*) * (idx + 1));
                for (int i = 0; i < irTempSize; i++) {
                    newtmp[i] = irTemp[i];
                }
                irTempSize = idx + 1;
                irTemp = newtmp;
            }
        }
        return irTemp[idx];
    }
};




class WriteMap {
    IRSB const* irsb;
    struct Bms {
        IRExpr* address;
        IRExpr* mem;
        UShort nb;
    };
    std::vector<Bms> unit;
public:
    WriteMap(IRSB const*bb):
        irsb(bb)
    {
        unit.reserve(10);
    }

    void Ist_Store(IRExpr *address, IRExpr* data) {
        IRType ty = typeOfIRExpr(irsb->tyenv, data);
        UShort dnb = sizeofIRType(ty);
        unit.emplace_back(Bms{ address, data, dnb });
    }
};

class GraphView{
    State& m_state;
public:
    GraphView(State& state):
        m_state(state)
    {
    }
    IRSB* BB2IR();
    inline IRExpr* tIRExpr(IRExpr* e);
    void run();
};



class StateAnalyzer {
    State& m_state;
public:
    StateAnalyzer(State& state) :
        m_state(state)
    {
    }


    void Run();

};