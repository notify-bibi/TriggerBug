#include "QCFGGraphicsTextItem.h"


QCFGGraphicsTextItem::QCFGGraphicsTextItem(QCFGStateView *parent, TextItemType type)
	:QGraphicsTextItem(parent),
	m_itemType(type)
{
}


QCFGGraphicsTextItem::~QCFGGraphicsTextItem()
{
}

int QCFGGraphicsTextItem::type() const { return QCFGGraphicsTextItem_Type; }

TextItemType QCFGGraphicsTextItem::itemType() const { return m_itemType; }