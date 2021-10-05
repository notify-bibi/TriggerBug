#include "QCFGGraphicsView.h"
#include "QCFGGraphicsScene.h"
#include "QCFGGraphicsView.h"
#include "QCFGStateView.h"
#include "QCFGBasictypes.h"
#include "QCFGGraphicsTextItem.h"
#define VIEW_CENTER viewport()->rect().center()
#define VIEW_WIDTH  viewport()->rect().width()
#define VIEW_HEIGHT viewport()->rect().height()


QCFGGraphicsView::QCFGGraphicsView(QCFGGraphicsScene *Scene, QWidget *parent)
	:QGraphicsView(Scene, parent),
	m_scene(Scene),
	m_scale(1.0),
	m_lMousePress(false),
	m_zoomDelta(0.1),
	m_ChooseState(NULL)
{
	Scene->installEventFilter(this);
	setHorizontalScrollBarPolicy(Qt::ScrollBarAlwaysOff);
	setVerticalScrollBarPolicy(Qt::ScrollBarAlwaysOff);
	setCursor(Qt::PointingHandCursor);
	setRenderHint(QPainter::Antialiasing, true);
	setSceneRect(INT_MIN / 2, INT_MIN / 2, INT_MAX, INT_MAX);
	centerOn(100, 100);
}

void QCFGGraphicsView::mousePressEvent(QMouseEvent *event)
{
	if (event->button() == Qt::LeftButton) {
		// 当光标底下没有 item 时，才能移动
		QPointF point = mapToScene(event->pos());
		if (scene()->itemAt(point, transform()) == NULL) {
			m_lMousePress = true;
			m_lastMousePos = event->pos();
		}
	}
	QGraphicsView::mousePressEvent(event);
}
void QCFGGraphicsView::mouseReleaseEvent(QMouseEvent *event)
{
	if (event->button() == Qt::LeftButton) {
		m_lMousePress = false;
		m_lastMousePos = event->pos();
	}
	QGraphicsView::mouseReleaseEvent(event);
}

void QCFGGraphicsView::mouseMoveEvent(QMouseEvent *event)
{
	if (m_lMousePress) {
		QPointF mouseDelta = mapToScene(event->pos()) - mapToScene(m_lastMousePos);
		move(mouseDelta);
		m_lastMousePos = event->pos();
	}
	QGraphicsView::mouseMoveEvent(event);
}
void QCFGGraphicsView::wheelEvent(QWheelEvent *event)
{
	setTransformationAnchor(QGraphicsView::AnchorUnderMouse);
	if (event->delta() > 0) {
		if(m_scale<20){
			scale(1.0 + m_zoomDelta, 1.0 + m_zoomDelta);
			m_scale *= 1.0 + m_zoomDelta;
		}
	}
	else {
		if (m_scale > 0.04) {
			scale(1.0 - m_zoomDelta, 1.0 - m_zoomDelta);
			m_scale *= 1.0 - m_zoomDelta;
		}
	}
}

void QCFGGraphicsView::move(QPointF delta)
{
	delta *= m_scale; 
	// view 根据鼠标下的点作为锚点来定位 scene
	setTransformationAnchor(QGraphicsView::AnchorUnderMouse);
	QPoint newCenter(VIEW_WIDTH / 2 - delta.x(), VIEW_HEIGHT / 2 - delta.y());
	centerOn(mapToScene(newCenter));

	// scene 在 view 的中心点作为锚点
	setTransformationAnchor(QGraphicsView::AnchorViewCenter);
}
bool QCFGGraphicsView::eventFilter(QObject* object, QEvent* event) 
{
	QGraphicsSceneMouseEvent* mouseEvent = static_cast<QGraphicsSceneMouseEvent*>(event);

	switch (static_cast<qint32>(event->type()))
	{
	case QEvent::GraphicsSceneMousePress:
	{
		switch (mouseEvent->button())
		{
		case Qt::LeftButton:
		{
			
			QGraphicsItem* item = scene()->itemAt(mouseEvent->scenePos().toPoint(), transform());
			if (!item)
				break;
			switch (item->type()) {
			case QCFGStateView_Type:
				m_ChooseState = (QCFGStateView*)item;
				break;
			case QCFGPathConnect_Type:
				qDebug() << "QCFGPathConnect_Type" << item;
				break;
			case QCFGGraphicsTextItem_Type:
				m_ChooseState = (QCFGStateView*)(item->parentItem());
				switch (((QCFGGraphicsTextItem*)item)->itemType()) {
				case TextItemCompressButton:
					break;
				case TextItemStartButton:
					m_ChooseState->start(); 
					m_ChooseState->updateConnect(mouseEvent->scenePos());
					m_ChooseState = NULL;
					break;
				case TextItemDeleteButton:
				}
				break;
			}

			break;
		}

		case Qt::RightButton:
		{

			QGraphicsItem* item = scene()->itemAt(mouseEvent->scenePos().toPoint(), transform());
			if (!item)
				break;
			switch (item->type()) {
			case QCFGStateView_Type:
				break;
			case QCFGPathConnect_Type:
				qDebug() << "QCFGPathConnect_Type" << item;
				break;
			}

			break;
		}
		}
		break;
	}

	case QEvent::GraphicsSceneMouseMove:
	{
		if (m_ChooseState) {
			m_ChooseState->updateConnect(mouseEvent->scenePos());
		}
		break;
	}

	case QEvent::GraphicsSceneMouseRelease:
	{

		if (m_ChooseState) {
			m_ChooseState->updateConnect(mouseEvent->scenePos());
			m_ChooseState = NULL;
		}
		break;
	}
	}


	return QObject::eventFilter(object, event);
}



QCFGGraphicsView::~QCFGGraphicsView()
{
}
