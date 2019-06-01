module CAudacity

open util/ordering[Time]
open BFContainer


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig Track extends BFContainer {
	_tracks : set Time
}

one sig Clipboard extends BFContainer {}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Inv[t : Time] {
	// all the blocks in DirManager are the blocks from Tracks and Clipboard
	// Others?
}

pred Init[t : Time] {
	no _tracks.t
	no Clipboard._blocks.t
}

pred Import[t, t' : Time, track : Track] {
	// Precondition
	track !in _tracks.t // this is a new track that doesn't belongs to the prject's tracks list
	some track._blocks.t // the new track is not empty
	all block : BlockFile | block in Int.(track._blocks.t) => some block._samples

	// Preserved
	_blocks.t' = _blocks.t

	// Updated
	_tracks.t' = _tracks.t + track
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


////////////////////////////////////////////////////////////////////////////////////////////
//                                                   Facts                                                   //
////////////////////////////////////////////////////////////////////////////////////////////

fact {
	Init[first]
	all t, t' : Time | t -> t' in next => 
		some track : Track |
			Import[t, t', track]
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
