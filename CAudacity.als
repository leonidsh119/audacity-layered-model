module CAudacity

open util/ordering[Time]
open BFContainer


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

one sig Clipboard extends BFContainer {}

sig Track extends BFContainer {
	_tracks : set Time,
	_window : Window
}

fact { // TODO: Add to sig
	_window in Track one -> Window
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Inv[t : Time] {
    // Track has at least 2 samples
	all track : _tracks.t | countAllSamples[track, t] > 1

	// Window's indices are in boundaries of tracks samples sequence and has at least 2 visible samples
	all track : _tracks.t |  #(track._window._winsamples.t) > 1 &&
								track._window._start.t >= 0 && 
								track._window._end.t > track._window._start.t &&
								(track._window._end.t).sub[track._window._start.t].add[1] = #(track._window._winsamples.t)

	// Window's start index is smaller than window's end index and their difference equals to the amount of visible samples
	all track : _tracks.t | track._window._end.t < countAllSamples[track, t]

	// All samples in window are from samples of track in the window's range
	all track : _tracks.t | track._window._winsamples.t = readSamples[track, track._window._start.t, track._window._end.t, t]

	// Validate history 
	Equiv[t, current[t]]
}

pred Equiv[t1 : Time, t2 : Time] {
	all cont : Track + Clipboard | Preserve[cont, t1, t2]
	_tracks.t1 = _tracks.t2
	_start.t1 = _start.t2
	_end.t1 = _end.t2
	_winsamples.t1 = _winsamples.t2
}

pred ChangeHistory[t, t' : Time] {
	History._history.t' = ((History._history.t).subseq[0, History._present.t]).add[t']  
	History._present.t' = (History._present.t).add[1] 
}

pred Init[t : Time] {
	no _tracks.t
	Empty[Clipboard, t]
	History._history.t = 0 -> t
	History._present.t = 0	
	_action.t = InitAction
}

pred Import[t, t' : Time, track : Track] {
	// Precondition
	track !in _tracks.t // this is a new track that doesn't belongs to the prject's tracks list
	Validate[track, t]

	// Preserved
	all cont : Track + Clipboard | Preserve[cont, t, t']

	// Updated
	_tracks.t' = _tracks.t + track
	_start.t' = _start.t ++ track._window -> 0 // Maximum zoom out
	_end.t' = _end.t ++ track._window -> lastContSampleIdx[track, t] // Maximum zoom out
	_winsamples.t' = _winsamples.t ++ track._window -> readAllSamples[track, t] // Maximum zoom out
	_action.t' = ImportAction
	ChangeHistory[t, t']
}

pred CutNoMove[t, t' : Time, track : Track, from, to : Int] {

}

pred CutMove[t, t' : Time, track : Track, from, to : Int] {

}

pred CutZoomIn[t, t' : Time, track : Track, from, to : Int] {

}

pred Cut[t, t' : Time, track : Track, from, to : Int] {
// Abstract Model
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	from <= to // there are at least one sample selected to cut
	from >= 0
	to <= countAllSamples[track, t]

	// Preserved
	_tracks.t' = _tracks.t
	all otherTrack : _tracks.t' - track | readAllSamples[otherTrack, t'] = readAllSamples[otherTrack, t]

// Concrete Model
	let firstCutBlockIndex = blockIndexForSampleIndex[track, from, t],  lastCutBlockIndex = blockIndexForSampleIndex[track, to, t] | {
		// Precondition
		all block : track._blocks.t | #(block._samples) > 0
		sampleIndexInBlockForSampleIndex[track, from, t] = 0 // "from" is the first sample in its block
		sampleIndexInBlockForSampleIndex[track, to, t] = sub[#(blockForBlockIndex[track, lastCutBlockIndex, t]._samples), 1] // "to" is the last sample in its block
		countAllBlocks[Clipboard, t] = sub[lastCutBlockIndex, firstCutBlockIndex] // required number of blocks in clipboard. what skip action achieves that?

		// Preserved
		_blocks.t' = _blocks.t
		all otherTrack : _tracks.t' - track, block : otherTrack._blocks | block.t'._samples = block.t._samples
		all i : range[0, countAllBlocks[track, t]] - range[firstCutBlockIndex, lastCutBlockIndex] | blockForBlockIndex[track, i, t']._samples = blockForBlockIndex[track, i, t]._samples

		// Updated
		all i : range[firstCutBlockIndex, lastCutBlockIndex] | no blockForBlockIndex[track, i, t']._samples
		all i : range[firstCutBlockIndex, lastCutBlockIndex] | blockForBlockIndex[Clipboard, sub[i, firstCutBlockIndex], t']._samples = blockForBlockIndex[track, i, t]._samples
	}
}

// NOTE: this operation has stronger precondition than in abstract model to ensure that all the required effects of Skip functions is done.
// However the Update part is the same.
pred Paste[t, t' : Time, track : Track, into : Int] {
// Abstract Model
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	into >= 0
	into <= countAllSamples[track, t]

	// Preserved
	_tracks.t' = _tracks.t
	all otherTrack : _tracks.t' - track | readAllSamples[otherTrack, t'] = readAllSamples[otherTrack, t]

// Concrete Model
	let firstEmptyBlockIndex = add[blockIndexForSampleIndex[track, sub[into, 1], t], 1],  lastEmptyBlockIndex = add[firstEmptyBlockIndex, countAllBlocks[Clipboard, t]] | {
		// Precondition
		all i : range[firstEmptyBlockIndex, lastEmptyBlockIndex] | #(blockForBlockIndex[track, i, t]._samples) = 0
		all i : range[0, countAllBlocks[track, t]] - range[firstEmptyBlockIndex, lastEmptyBlockIndex] | #(blockForBlockIndex[track, i, t]._samples) > 0

		// Preserved
		_blocks.t' = _blocks.t
		all otherTrack : _tracks.t' - track, block : otherTrack._blocks | block.t'._samples = block.t._samples
		all block : Clipboard._blocks | block.t'._samples = block.t._samples
		all i : range[0, countAllBlocks[track, t]] - range[firstEmptyBlockIndex, lastEmptyBlockIndex] | blockForBlockIndex[track, i, t']._samples = blockForBlockIndex[track, i, t]._samples

		// Updated
		all i : range[firstEmptyBlockIndex, lastEmptyBlockIndex] | blockForBlockIndex[track, i, t']._samples = blockForBlockIndex[Clipboard, sub[i, firstEmptyBlockIndex], t]._samples
	}
}

pred ZoomIn[t , t' : Time, track : Track, newStart, newEnd : Int] {
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	#(track._window._winsamples.t) > 2 // the window can shrink
	newEnd.sub[newStart] < (track._window._end.t).sub[track._window._start.t] // new window is smaller than the old one
	newStart >= 0 // new window boundaries are inside the track's samples (start)
	newStart >= track._window._start.t // new window boundaries are inside old one's (start)
	newEnd <= track._window._end.t // new window boundaries are inside old one's (end)
	newEnd.sub[newStart] > 1 // new window will have the minimum required size
	
	// Preserved
	_tracks.t' = _tracks.t
	all cont : Track + Clipboard | Preserve[cont, t, t']

	// Updated
	_start.t' = _start.t ++ track._window -> newStart
	_end.t' = _end.t ++ track._window -> newEnd
	_winsamples.t' = _winsamples.t ++ track._window -> readSamples[track, newStart, newEnd, t]
	_action.t' = ZoomInAction
	ChangeHistory[t, t']
}

pred ZoomOut[t , t' : Time, track : Track, newStart, newEnd : Int] {
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	(#(track._window._winsamples.t)).sub[countAllSamples[track, t]]  > 0  // the window can grow
	newEnd.sub[newStart] > (track._window._end.t).sub[track._window._start.t] // new window is larger than the old one
	newStart <= track._window._start.t // new window boundaries are outside old one's (start)
	newEnd >= track._window._end.t // new window boundaries are outside old one's (end)
	newStart >= 0 // new window boundaries are inside the track's samples (start)
	newEnd < countAllSamples[track, t] // new window boundaries are inside the track's samples (end)
	newStart < newEnd // new window is a positive range

	// Preserved
	_tracks.t' = _tracks.t
	all cont : Track + Clipboard | Preserve[cont, t, t']

	// Updated
	_start.t' = _start.t ++ track._window -> newStart
	_end.t' = _end.t ++ track._window -> newEnd
	_winsamples.t' = _winsamples.t ++ track._window -> readSamples[track, newStart, newEnd, t]
	_action.t' = ZoomOutAction
	ChangeHistory[t, t']
}

pred Split[cont : BFContainer, blockIdx : Int, head, tail : BlockFile, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	(#(head._samples)).add[#(tail._samples)] > 1

	let block = blockForBlockIndex[cont, blockIdx, t] | {
		// Precondition
		block._samples = append[head._samples, tail._samples]

		// Preserved
		all bfc : BFContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
		_tracks.t' = _tracks.t

		// Updated
		_blocks.t' = _blocks.t ++ cont -> insert[insert[cont._blocks.t, blockIdx, tail], blockIdx, head]
	}
}

pred Insert[cont : BFContainer, blockIdx : Int, emptyBlock : BlockFile, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	#(emptyBlock._samples) = 0

	// Preserved
	all bfc : BFContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
	_tracks.t' = _tracks.t

	// Updated
	_blocks.t' = _blocks.t ++ cont -> insert[cont._blocks.t, blockIdx, emptyBlock]
}

pred Delete[cont : BFContainer, blockIdx : Int, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	#(blockForBlockIndex[cont, blockIdx, t]._samples) = 0

	// Preserved
	all bfc : BFContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
	_tracks.t' = _tracks.t

	// Updated
	_blocks.t' = _blocks.t ++ cont -> delete[cont._blocks.t, blockIdx]
}

pred Preserve[t, t' : Time] {
	all cont : Track + Clipboard | Preserve[cont, t, t']
	_tracks.t' = _tracks.t
	_start.t' = _start.t
	_end.t' = _end.t
	_winsamples.t' = _winsamples.t
	_history.t' = _history.t
	_present.t' = _present.t
	_action.t' = SkipAction
}

pred Undo[t, t' : Time] {
	// Precondition
	History._present.t > 0

	// Preserved
	History._history.t' = History._history.t

	// Updated
	History._present.t' = (History._present.t).sub[1]
	Equiv[t', current[t']]
	_action.t' = UndoAction
}

pred Redo[t, t' : Time] {
	// Precondition
	History._present.t < (#(History._history.t)).sub[1]

	// Preserved
	History._history.t' = History._history.t

	// Updated
	History._present.t' = (History._present.t).add[1]
	Equiv[t', current[t']]
	_action.t' = RedoAction
}

pred SystemOperation[t, t' : Time] {
		some track : Track, i, j : Int |
			Import[t, t', track]
			or Cut[t, t', track, i, j]
			or Paste[t, t', track, i]
			or ZoomIn[t, t', track, i, j]
			or ZoomOut[t, t', track, i, j]
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                   Facts                                                   //
////////////////////////////////////////////////////////////////////////////////////////////

fact {
	Init[first]
	all t, t' : Time | t -> t' in next => 
		(SystemOperation[t, t'] and ChangeHistory[t, t']) 
		or Undo[t, t'] 
		or Redo[t, t']
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                              Assertions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

run { 
	#(BlockFile._samples) >= 2
} for 7 but 3 Time, 7 Int

check {
	all t : Time | Inv[t]
} for 5
