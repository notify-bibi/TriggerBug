#include "QCFGPathConnect.h"
#include "QCFGStateView.h"

#include <QGraphicsView>
#include <QtWidgets>
#include <QPen>

#include <QGraphicsScene>
#include <QFontMetrics>
#include <QPen>
QCFGPathConnect::QCFGPathConnect(QCFGStateView *stateView, QCFGStateView *branch)
	:QGraphicsPathItem(stateView),
	m_ConnectState(branch),
	thisStateView(stateView)
{
	setFlag(QGraphicsItem::ItemIsMovable);
	setFlag(QGraphicsItem::ItemIsSelectable);
	setFlag(QGraphicsItem::ItemSendsScenePositionChanges);
	setCacheMode(DeviceCoordinateCache);
	

}
void QCFGPathConnect::onDraw() {
	/*QPointF StartVector(50, 100);
	QPointF EndVector(50, 0);*/

	QPointF StartVector(thisStateView->m_width/2, thisStateView->m_height);
	QPointF EndVector(thisStateView->m_width / 2, 0);

	QPointF Vector(m_ConnectState->scenePos() - scenePos() + EndVector - StartVector);
	// ÉèÖÃ»­±Ê¡¢»­Ë¢
	QPen pen = this->pen();
	pen.setWidth(1);
	pen.setColor(QColor(230, 155, 6));
	setPen(pen);
	setBrush(Qt::NoBrush);

	QPainterPath starPath(StartVector);
	starPath.cubicTo(
		QPointF(Vector.rx()*0.25, Vector.ry()*0.45) + StartVector,
		QPointF(Vector.rx()*0.75, Vector.ry()*0.55) + StartVector,
		Vector + StartVector
	);
	setPath(starPath);
}
int QCFGPathConnect::type() const { return QCFGPathConnect_Type; }

QCFGPathConnect::~QCFGPathConnect()
{
}
