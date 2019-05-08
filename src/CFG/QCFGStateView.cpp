#include "QCFGStateView.h"
#include "QCFGPathConnect.h"
#include "QCFGGraphicsTextItem.h"
#include "CFG.h"
extern CFG *global_w;

QCFGStateView::QCFGStateView(QCFGGraphicsScene *Scene,State* state)
	:QGraphicsPathItem(NULL),
	m_state(state),
	m_scene(Scene),
	m_father(NULL),
	m_width(0),
	m_height(0)

{
	setFlag(QGraphicsItem::ItemIsSelectable);
	setCacheMode(DeviceCoordinateCache);
	setFlag(QGraphicsItem::ItemIsMovable);


	setPen(QPen(QColor(255, 255, 0)));
	this->setBrush(QBrush(QColor(0, 160, 230)));

	addTextItem(QString("Start"), TextItemStartButton);
	addTextItem(QString("Compress"), TextItemCompressButton);
	addTextItem(QString("Delete"), TextItemDeleteButton);
}

QCFGStateView::~QCFGStateView()
{
}
int QCFGStateView::type() const { return QCFGStateView_Type; }

void QCFGStateView::updateConnect(QPointF &fpos) {
	auto result = updateConnection(fpos);
	qDebug() << fpos << result;
	fpos = fpos - QPointF((result.rx() - fpos.rx())*0.5, 0);
	updateConnection(fpos);
	Q_FOREACH(QGraphicsItem* childItem, childItems())
	{
		if (childItem->type() == QCFGPathConnect_Type) {
			((QCFGPathConnect*)childItem)->onDraw();
		}
	}
	if (m_father) {
		Q_FOREACH(QGraphicsItem* childItem, m_father->childItems())
		{
			if (childItem->type() == QCFGPathConnect_Type) {
				((QCFGPathConnect*)childItem)->onDraw();
			}
		}
	}
}


QPointF QCFGStateView::updateConnection(QPointF &fpos)
{
	if (branches.empty()) {
		setPos(fpos);
		return fpos+ QPointF(this->boundingRect().width(),0);
	}
	QPointF tfpos = fpos;
	for (auto branch : branches) {
		QPointF argPos = tfpos + QPointF(0, this->boundingRect().height()+20);
		auto result = branch->updateConnection(argPos);
		Q_FOREACH(QGraphicsItem* childItem, branch->childItems())
		{
			if (childItem->type() == QCFGPathConnect_Type) {
				((QCFGPathConnect*)childItem)->onDraw();
			}
		}
		tfpos += result- argPos;
	}
	QPointF offset = tfpos - fpos;
	setPos(tfpos.rx() - offset.rx() / 2- this->boundingRect().width()/2, fpos.ry());
	return tfpos;

}
void QCFGStateView::setParentState(QCFGStateView *parent) {
	if (!m_father) {
		m_father = parent;
	}
	else {
		Q_ASSERT(m_father==NULL);
	}
}

void QCFGStateView::Connect(QCFGStateView *branch)
{
	branch->setParentState(this);
	branches.emplace_back(branch);
	auto Con = new QCFGPathConnect(this, branch);
}

QGraphicsTextItem * QCFGStateView::addTextItem(QString &Str, TextItemType type) {
	QGraphicsTextItem *Text = new QCFGGraphicsTextItem(this, type);
	Text->setPlainText(Str);
	Text->setPos(0, m_height);
	auto nw = Text->boundingRect().width();
	if (nw > m_width) { m_width = nw; }
	m_height += Text->boundingRect().height();

	QPainterPath path;
	path.addRoundedRect(0, 0, m_width, m_height, 5, 5);
	setPath(path);

	return Text;
}

void QCFGStateView::start()
{
	m_state->start();
	for (auto son : m_state->branch) {
		this->Connect( global_w->addState(son) );
	}
}

void QCFGStateView::compress(unsigned long long)
{
}

void QCFGStateView::deleteState()
{
}
