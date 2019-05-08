#pragma once
#include <qgraphicsscene.h>
#include <QGraphicsView>
#include <QtWidgets>

class QCFGGraphicsScene :
	public QGraphicsScene

{
public:
	QCFGGraphicsScene();
	~QCFGGraphicsScene();
	void QCFGGraphicsScene::drawBackground(QPainter*, const QRectF&);
};

