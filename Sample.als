module Sample


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig Sample {}

sig ID {}

abstract sig Container {
	_id : ID
} 

fact {
	~_id in ID -> lone Container 	
}
