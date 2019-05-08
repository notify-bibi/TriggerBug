#pragma once
#include <QMainWindow>
#include <QtWidgets>
#include <QtWidgets/QWidget>
#include "QCFGGraphicsScene.h"
#include "QCFGGraphicsView.h"
#include "QCFGStateView.h"

class QCFGGraphicsView :
	public QGraphicsView
{
	Q_OBJECT
public:
	QCFGGraphicsView(QCFGGraphicsScene *Scene, QWidget *parent);
	void QCFGGraphicsView::mouseMoveEvent(QMouseEvent *event);
	void QCFGGraphicsView::wheelEvent(QWheelEvent *event);
	void QCFGGraphicsView::mousePressEvent(QMouseEvent *event);
	void QCFGGraphicsView::move(QPointF delta);
	void QCFGGraphicsView::mouseReleaseEvent(QMouseEvent *event);
	bool QCFGGraphicsView::eventFilter(QObject* object, QEvent* event);
	~QCFGGraphicsView();
private:
	qreal m_scale;// 缩放的比例
	qreal m_zoomDelta;// 缩放的增量
	QPoint m_lastMousePos;//平移last
	bool m_lMousePress;//左击
	QCFGGraphicsScene *m_scene;
	QCFGStateView *m_ChooseState;
};

