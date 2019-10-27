#pragma once
#include <QGraphicsItem.h>
#include "QCFGStateView.h"
#include "QCFGBasictypes.h"

class QCFGPathConnect :
	public QGraphicsPathItem
{
public:
	QCFGPathConnect(QCFGStateView *stateView, QCFGStateView *);
	void QCFGPathConnect::onDraw();
	int type() const;
	~QCFGPathConnect();
private:
	QCFGStateView *m_ConnectState;
	QCFGStateView *thisStateView;
};

