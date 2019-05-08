#include "QCFGGraphicsScene.h"



QCFGGraphicsScene::QCFGGraphicsScene()
	:QGraphicsScene()
{
}


void QCFGGraphicsScene::drawBackground(QPainter* painter, const QRectF& rect)
{
	painter->fillRect(rect, QBrush(QColor(3, 54, 73)));
	int Margin = 40;//ฑ฿ิต

	QPen linePen(QColor(80, 80, 80), 1, Qt::DotLine, Qt::FlatCap, Qt::RoundJoin);
	linePen.setCosmetic(true); // Performance optimization
	painter->setPen(linePen);

	for (int i = 0; i <= 20; i++)
	{
		int x = rect.left() + (i*(rect.width() - 1) / 20);
		painter->drawLine(x, rect.top(), x, rect.bottom());
	}
	for (int j = 0; j <= 10; j++)
	{
		int y = rect.bottom() - (j*(rect.height() - 1) / 10);
		painter->drawLine(rect.left() - 5, y, rect.right(), y);
	}

}


QCFGGraphicsScene::~QCFGGraphicsScene()
{
}

