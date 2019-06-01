module AContainer

open CommonAudacity

abstract sig AContainer extends Container {
	_samples : (seq Sample) -> Time
}

fact { // TODO: Add to sig
	_id in AContainer lone -> ID
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Empty[cont : AContainer, t : Time] {
	countAllSamples[cont, t] = 0
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

fun readAllSamples[cont : AContainer, t : Time] : seq Sample {
	cont._samples.t
}

fun readSamples[cont : AContainer, from, to : Int, t : Time] : seq Sample {
	subseq[cont._samples.t, from, to]
}

fun lastContSampleIdx[cont : AContainer, t : Time] : Int {
	countAllSamples[cont, t].sub[1]
}

fun countAllSamples[cont : AContainer, t : Time] : Int {
	#readAllSamples[cont, t]
}

fun countSamples[cont : AContainer, from, to : Int, t : Time] : Int {
	#readSamples[cont, from, to, t]
}
