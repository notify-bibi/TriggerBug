#include "CFG.h"
#include <QtWidgets/QApplication>
#include "../Engine/engine.hpp"
CFG *global_w;
int main(int argc, char *argv[])
{
	QApplication a(argc, argv);

	ThreadPool pool(4);
	
	CFG w;

	global_w = &w;


	const char *filename[] = { "C:\\Users\\bibi\\Desktop\\MemoryDump",".\\MemoryDump" };
	State state(filename, True);
	PAGE *page = state.getMemPage(0x7FFFF7DEC7B8);



#if 1
	auto sym = state.m_ctx.bv_const("Srdi", 8);
	state.regs.m_ast[72] = sym;
	SET1(state.regs.m_fastindex + 72, 1);
	//state.solv.add(ule(sym, 36));
	state.add_assert(uge(sym, 1), True);
	/*state.add_assert(ule( sym, 123), True);
	state.add_assert(sym==97, True);*/

#else

	auto sym = state.m_ctx.bv_val(97, 8);
	state.regs.m_ast[72] = sym;
	SET1(state.regs.m_fastindex + 72, 1);

#endif

	w.addState(&state);




	//std::cout << state << std::endl;

	//state.compress(0x0400ecd);

	//std::cout << state << std::endl;

	//auto fgghh = state.branch[1]->mem.Iex_Load(Variable(state.m_ctx, 0x007fffffffe2f0, 64), Ity_I8);

	////auto fgghh = state.branch[1]->mem.Iex_Load(Variable(state.m_ctx,0x007fffffffe2f0,64),Ity_I8);

	//std::vector<Z3_ast> result;
	//eval_all(result, state.branch[1]->solv, (expr)fgghh);



	//__m256i df = _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19);



	//std::cout << "over" << std::endl;



	



	w.show();
	return a.exec();
}
