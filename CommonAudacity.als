module CommonAudacity

sig Time {}

abstract sig Action {
	_action : set Time
}

one sig InitAction, ImportAction, CutNoMoveAction, CutMoveAction, CutZoomInAction, PasteAction, ZoomInAction , ZoomOutAction, UndoAction, RedoAction, SkipAction extends Action {}

sig Sample {}

sig ID {}

abstract sig Container {
	_id : ID
}


