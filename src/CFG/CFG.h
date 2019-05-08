#pragma once
#include <QMainWindow>
#include <QtWidgets>
#include <QGuiApplication>
#include <QGraphicsScene>
#include <QFileDialog>
#include <QtWidgets/QWidget>
#include "QCFGGraphicsScene.h"
#include "QCFGGraphicsView.h"
#include "../Engine/engine.hpp"


class CFG : public QMainWindow
{
	Q_OBJECT

public:
	CFG(QWidget *parent = Q_NULLPTR);
	QCFGStateView*  addState(State *state);
private:
	QMenu* m_fileMenu;
	QCFGGraphicsScene* m_CFGGraphicsScene;
	QCFGGraphicsView* m_CFGGraphicsView;
};
