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

sig Window {
	_start : Int -> Time,
	_end : Int -> Time,
	_winsamples : (seq Sample) -> Time
}

one sig History {
	_history : (seq Time) -> Time,
	_present : Int -> Time
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

fun current[t : Time] : Time {
	(History._history.t)[History._present.t]
}


