#include "CFG.h"
using namespace z3;

CFG::CFG(QWidget *parent)
	: QMainWindow(parent),
	m_CFGGraphicsScene(new QCFGGraphicsScene()),
	m_CFGGraphicsView(new QCFGGraphicsView(m_CFGGraphicsScene, parent))
{
	setCentralWidget(m_CFGGraphicsView);
	setWindowTitle(tr("State Manager"));
	
	m_CFGGraphicsView->setScene(m_CFGGraphicsScene);
	m_CFGGraphicsView->setStyleSheet("border:none; background:transparent;");

	resize(1080, 1080*1080/1920);
}

QCFGStateView* CFG::addState(State *state) {
	auto state1 = new QCFGStateView(m_CFGGraphicsScene, state);
	m_CFGGraphicsScene->addItem(state1);
	state1->updateConnect(QPointF(0, 0));
	return state1;
}