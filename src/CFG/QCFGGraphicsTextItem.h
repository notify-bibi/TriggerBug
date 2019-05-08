#pragma once
#include "QCFGStateView.h"
#include <qgraphicsitem.h>
#include "QCFGBasictypes.h"
class QCFGGraphicsTextItem :
	public QGraphicsTextItem
{
private:
	TextItemType m_itemType;
public:
	QCFGGraphicsTextItem(QCFGStateView *parent, TextItemType type);
	~QCFGGraphicsTextItem();
	int type() const;
	TextItemType itemType() const;
};

