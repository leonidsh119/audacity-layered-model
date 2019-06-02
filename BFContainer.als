module BFContainer

open CommonAudacity

let MAX_BLOCK_SIZE = 4

sig BlockFile {
	_samples : seq Sample
}{ 
	#_samples <= MAX_BLOCK_SIZE 
}

abstract sig BFContainer extends Container {
	_blocks : (seq BlockFile) -> Time
}

fact { // TODO: Add to sig
	_id in BFContainer lone -> ID
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Empty[cont : BFContainer, t : Time] {
	countAllSamples[cont, t] = 0
}

pred Validate[cont : BFContainer, t : Time] {
	some cont._blocks.t // Has some blocks
	all block : cont._blocks.t | some block._samples // No Empty blocks
}

pred Preserve[cont : BFContainer, t, t' : Time] {
	_blocks.t' = _blocks.t
	readAllSamples[cont, t] = readAllSamples[cont, t']
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

fun lastBlockIndex[cont : BFContainer, t : Time] : Int {
	countAllBlocks[cont, t].sub[1]
}

fun countBlocks[cont : BFContainer, from, to : Int, t : Time] : Int {
	#readBlocks[cont, from, to, t]
}

fun readBlocks[cont : BFContainer, from, to : Int, t : Time] : seq BlockFile {
	subseq[readAllBlocks[cont, t], from, to]
}

fun countAllBlocks[cont : BFContainer, t : Time] : Int {
	#readAllBlocks[cont, t]
}

fun readAllBlocks[cont : BFContainer, t : Time] : seq BlockFile {
	cont._blocks.t
}

fun countAllSamples[cont : BFContainer, t : Time] : Int {
	#readAllSamples[cont, t]
}

// NOTE: This method is the base for all the other operations on samples and so will be used in retrieve functional for refinement
fun readAllSamples[cont : BFContainer, t : Time] : seq Sample {
	let blocksCount = #(cont._blocks.t), lastSampleIndex = prec[cont, blocksCount, t] |
		readSamples[cont, 0, lastSampleIndex, t]
}

fun countSamples[cont : BFContainer, from, to : Int, t : Time] : Int {
	#readSamples[cont, from, to, t]
}

fun readSamples[cont : BFContainer, from, to : Int, t : Time] : seq Sample {
	// add/sub are needd to align indices from [from, to] range into zero-starting range
	{ i : range[0, to.sub[from].add[1]], sample : readSample[cont, i.add[from], t] }
}

fun lastContSampleIdx[cont : BFContainer, t : Time] : Int {
	countAllSamples[cont, t].sub[1]
}

// For the given sample index in the entire track provides the block index the sample belongs to
fun readSample[cont : BFContainer, sampleIdx : Int, t : Time] : Sample {
	blockForSampleIndex[cont, sampleIdx, t]._samples[sampleIndexInBlockForSampleIndex[cont, sampleIdx, t]]
}

// For the given sample index in the entire track provides the block the sample belongs to
fun sampleIndexInBlockForSampleIndex[cont : BFContainer, sampleIdx : Int, t : Time] : Int {
	sampleIdx.sub[prec[cont, blockIndexForSampleIndex[cont, sampleIdx, t], t]]
}

// For the given sample index in the entire track provides the block the sample belongs to
fun blockForSampleIndex[cont : BFContainer, sampleIdx : Int, t : Time] : BlockFile {
	let blockIdx = blockIndexForSampleIndex[cont, sampleIdx, t] |
		blockForBlockIndex[cont, blockIdx, t]
}

fun blockForBlockIndex[cont : BFContainer, blockIdx : Int, t : Time] : BlockFile {
		(cont._blocks.t)[blockIdx]
}

// For the given sample index in the entire track provides the block index the sample belongs to
fun blockIndexForSampleIndex[cont : BFContainer, sampleIdx : Int, t : Time] : Int {
	// (cont._blocks.t).BlockFile - the indices list of the blocks in sequence
	max[ { j : (cont._blocks.t).BlockFile | prec[cont, j, t] <= sampleIdx } ] // Calculates the highest index of blocks where the sample can appear 
}

// Count the number of samples in block subsequence from start upto blockIdx (not including).
// This is actually the index of the first sample in the block j
fun prec[cont : BFContainer, blockIdx : Int, t : Time] : Int {
	sum k : range[0, blockIdx] | #((cont._blocks.t)[k]._samples)
}

// Creates a list of integers in range [from, to)
fun range[from, upto : Int] : set Int {
	{ n : Int | from <= n && n < upto } // This is the technique to create an iteration: create a list of integers representing the interation indices
}
