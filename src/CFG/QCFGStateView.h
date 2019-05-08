#pragma once
#include <QPen>
#include "../Engine/engine.hpp"
#include <QGraphicsScene>
#include <QFontMetrics>
#include <QPainter>
#include <Qstring>
#include <QStyleOptionGraphicsItem>
#include <qgraphicsitem.h>
#include "QCFGGraphicsScene.h"
#include "QCFGBasictypes.h"

class QCFGStateView :
	public QGraphicsPathItem
{
public:
	qreal m_width;
	qreal m_height;
	QCFGStateView(QCFGGraphicsScene *, State *state);
	~QCFGStateView();
	int type() const;
	void Connect(QCFGStateView *branch);
	void setParentState(QCFGStateView *);
	QGraphicsTextItem * addTextItem(QString &Str, TextItemType type);
	QPointF updateConnection(QPointF &);
	void updateConnect(QPointF &fpos);
	void start();
	void compress(unsigned long long);
	void deleteState();
private:
	QCFGGraphicsScene *m_scene;
	std::vector<QCFGStateView*> branches;
	QCFGStateView *m_father;
	State *m_state;
};

