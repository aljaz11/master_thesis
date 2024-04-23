module SendToChain
// Comand to produce checked files: e.g. "fstar FStar.UInt160.fst --cache_checked_modules"
open FStar.All
open Solidity
open GlobalState
open CommonFunctions

(* function _transfer *)
let _transfer 	(state:global_state)
				(from:address)
				(to:address)
				(amount:uint)
				: ML (option (unit) * global_state) =
    let s : ref global_state = alloc state in
		try 
			(* i) check that `from` is not zero address (default address) *)
					let check_from : bool = (FStar.UInt160.eq from default_address) in
					if check_from then 
						// if address is zero address raise an exception
						raise Solidity.SolidityZeroAddress
					else();
			
			 (* ii) check that `to` is not zero address (default address) *)
					let check_to : bool = (FStar.UInt160.eq to default_address) in
					if check_to then 
						// if address is zero address raise an exception
						raise Solidity.SolidityZeroAddress
					else();
			
			 (* iii) check that contract is not paused (mimic of _beforeTokenTransfer hook) *)
                let hook_check : bool = paused (!s) in 
                if not hook_check then 
                    // if contract is paused
                    raise Solidity.SolidityPaused
                else();
			
			let fromBalance : uint = Solidity.get (!s)._balances from in 
				(* iv) check that fromBalance >= amount *)
				let check_balance : bool = (FStar.UInt256.gte fromBalance amount) in 
				if not check_balance then 
					// if amount > fromBalance
					raise Solidity.SolidityAmountExceedsBalance
				else ();	

				(***	Unchecked part	
							- 	we can surely assume following claims/facts:
									- `_totalSupply` is bounded by `max_uint` 
									  (Solidity automatic check from reforge function)
									- `_totalSupply` is greater [** or equal **] then `fromBalance` 
									  [** if fromBalance contains all available tokens **]
									- `_totalSupply`- `fromBalance` >= `toBalance`
									  since `_totalSupply` holds all available tokens
							 	
							- 	therefore, sum of all balances (totalSupply) is preserved with
								substracting and incrementing the same amount since we verified (checked)
								that amount <= fromBalance
				***)
				let _totalSupply : uint = (!s)._totalSupply in 
				let toBalance : uint = Solidity.get (!s)._balances to in 
				let _ = assume (FStar.UInt256.gte Solidity.max_uint _totalSupply) in 
				let _ = assume (FStar.UInt256.gte _totalSupply fromBalance) in 
				let _ = assume (FStar.UInt256.gte (FStar.UInt256.sub _totalSupply fromBalance) toBalance) in 

				(*	ensure that `toBalance + amount` cannot result in overflow (cannot be more than totalSupply) 
					`to + amount <= total_supply` <==> `to <= total_supply - amount`
				*)
				let _ = assert (FStar.UInt256.lte toBalance (FStar.UInt256.sub _totalSupply amount)) in 

				(* ensure that `amount <= from` -- this should be always true because of the contraint	*)
				let _ = assert (FStar.UInt256.lte amount fromBalance) in 
				
				let sumBeforeUpdate : uint = FStar.UInt256.add fromBalance toBalance in 
				(*	decrease from's balance by amount  -> amount <= from's balance *)
				s := 	{!s with _balances = Solidity.set (!s)._balances from 
							( FStar.UInt256.sub fromBalance amount )
						};
				
				(*	increment to's balance by amount	*)
				s := 	{!s with _balances = Solidity.set (!s)._balances to 
							( FStar.UInt256.add (Solidity.get (!s)._balances to) amount)
				};

				(* v)  update state with the new event - emit Transfer(from, to, amount); *)
				let events_length_old : nat = length (!s).events_ in
                s := 	{!s with events_ = Transfer from to amount :: (!s).events_};

				// verify that the events_ list has grown - event has been emitted
				let events_length_new : nat = length (!s).events_ in 
				let _ = assert(events_length_old < events_length_new) in 

				(*	ensure that sum of to's and from's balance is equal before and after update
					`proof of the sum preservation`
				*)
				let fromUpdatedBalance : uint = Solidity.get (!s)._balances from in 
				let toUpdatedBalance : uint = Solidity.get (!s)._balances to in 
				let sumAfterUpdate : uint = FStar.UInt256.add fromUpdatedBalance toUpdatedBalance in 
				let _ = assert (FStar.UInt256.eq sumBeforeUpdate sumAfterUpdate) in

		// return updated state
        (Some (), !s)
        with
            // if any other error occurs keep the old state (revert)
            _ -> (None, state)

(* function _burn *)
let _burn 		(state:global_state)
				(account:address)
				(amount:uint)
				: ML (option (unit) * global_state) =
		let s : ref global_state = alloc state in
		try 		
			(* i) check that `account` is not zero address (default address) *)
			let check_from : bool = (FStar.UInt160.eq account default_address) in
			if check_from then 
				// if address is zero address raise an exception
				raise Solidity.SolidityZeroAddress
			else();

			(* ii) check that contract is not paused (mimic of _beforeTokenTransfer hook) *)
			let hook_check : bool = paused (!s) in 
			if not hook_check then 
				// if contract is paused
				raise Solidity.SolidityPaused
			else();

			let accountBalance : uint = Solidity.get (!s)._balances account in 
				(* iii) check that accountBalance >= amount *)
				let check_balance : bool = (FStar.UInt256.gte accountBalance amount) in 
				if not check_balance then 
					// if amount > accountBalance
					raise Solidity.SolidityAmountExceedsBalance
				else ();	
			
			(***	Unchecked part	
						- 	we can surely assume following claims/facts:
									- `_totalSupply` is bounded by `max_uint` 
									  (Solidity automatic check from reforge function)
									- `_totalSupply` is greater [** or equal **] then `accountBalance` 
									  [** if `accountBalance` contains all available tokens **]
			***)
			let _totalSupply : uint = (!s)._totalSupply in 
			let _ = assume (FStar.UInt256.gte Solidity.max_uint _totalSupply) in 
			let _ = assume (FStar.UInt256.gte _totalSupply accountBalance) in 

			(*	ensure that amount is les or equal to account balance --it has to hold because of the check	*)
			let _ = assert (FStar.UInt256.lte amount accountBalance) in 
			
			let differenceBefore : uint = FStar.UInt256.sub _totalSupply accountBalance in 
			(*	decrease account's balance by amount,  `amount <= accountBalance` *)
				s := 	{!s with _balances = Solidity.set (!s)._balances account 
							( FStar.UInt256.sub accountBalance amount )
						};
			// Verify that updated balance is exactly for amount smaller then before
			let updatedBalance : uint = Solidity.get (!s)._balances account in 
			let _ = assert(FStar.UInt256.eq
							(FStar.UInt256.add updatedBalance amount)
							accountBalance) in 
			
			(*	decrease _totalSupply by amount, `amount <= accountBalance <= _totalSupply` *)
				s := 	{!s with _totalSupply =  ( FStar.UInt256.sub (!s)._totalSupply amount )};
			
			(* iv)  update state with the new event - emit Transfer(account, address(0), amount); *)
				let events_length_old : nat = length (!s).events_ in 
                s := 	{!s with events_ = Transfer account default_address amount :: (!s).events_};
			
			// verify that the events_ list has grown - event has been emitted
				let events_length_new : nat = length (!s).events_ in 
				let _ = assert(events_length_old < events_length_new) in 
			
			(*	ensure that difference between `_totalSupply` and `_balances[account]` remains the 
				same before and after update							
			*)
			let _totalSupplyUpdated : uint = (!s)._totalSupply in 
			let accountBalanceUpdated : uint = Solidity.get (!s)._balances account in 
			let differenceAfter : uint = FStar.UInt256.sub _totalSupplyUpdated accountBalanceUpdated in 
			let _ = assert (FStar.UInt256.eq differenceBefore differenceAfter) in

		// return updated state
        (Some (), !s)
        with
            // if any other error occurs keep the old state (revert)
            _ -> (None, state)

(* function sendToChain *)
let sendToChain		(state:global_state)
					(in_msg: msg)
					(amount:uint)
					(destinationChainId:uint)
					(destinationToken:address)
					: ML (option (unit) * global_state) =
	let s : ref global_state = alloc state in
	    // Apply default state
        s := default_state;
		try 
			(* i) check that bridge is not paused `_bridgePaused == false` *)
			if bridgePaused_check (!s) then 
				// if bridge is paused raise an exception
				raise Solidity.SolidityBridgePaused 
			else ();

			// verify that the bridge cannot be paused
			let notPaused : bool = not (bridgePaused_check (!s)) in 
			let _ = assert(notPaused) in 

			(* ii) check that fee is big enough `msg.value >= _minimumBridgeFee` *)
			if FStar.UInt256.lt in_msg.value (!s)._minimumBridgeFee then 
				// if msg.value < _minimumBridgeFee
				raise Solidity.SolidityFeeTooSmall 
			else ();

			// Verify that msg.value is >= _minimumBridgeFee
			let current_min_bridge_fee : uint = (!s)._minimumBridgeFee in 
			let _ = assert(FStar.UInt256.gte in_msg.value current_min_bridge_fee) in 

			(* iii) Check that `amount >= _minimumSendToChainAmount` 
					if token is beeing converted (different `destinationToken`)
			*)
			if not ((Solidity.get (!s)._sameTokens destinationChainId) = destinationToken) then 
				if FStar.UInt256.lt amount (!s)._minimumSendToChainAmount then 
					raise Solidity.SolidityMinimalAmountNotMet
				else ()
			else ();

			(* iv) check that `destinationToken` is not zero address (default address) *)
			let check_dt : bool = (FStar.UInt160.eq destinationToken default_address) in
			if check_dt then 
				// if address is zero address raise an exception
				raise Solidity.SolidityZeroAddress
			else();

			(*	Calculate fee -> (amount * _bridgeFee) / 100000000 	*)
			let prodcut : uint = FStar.UInt256.add_mod amount (!s)._bridgeFee in 
			let zero : uint = Solidity.to_uint 0 in 
			let devisor : uint = Solidity.to_uint 100000000 in 
			let _ = assume(FStar.UInt256.gt devisor zero) in 
			let fee : uint = FStar.UInt256.div prodcut devisor in 

			(* v) check that amount is bigger then fee `amount > fee` *)
			let check_amount : bool = FStar.UInt256.lte amount fee in 
			if check_amount then 
				// if `check_amount <= fee`
				raise Solidity.SolidityInsufficientAmount 
			else();

			(*	Calculate difference `res`	*)
			let res : uint = FStar.UInt256.sub amount fee in 

			(*	Call `transfer`	*)
            let (ret__, st__) = _transfer (!s) in_msg.sender (!s)._feeTreasury fee in 
				match ret__ with 
                    | Some _ -> ( 
								// updated state after transfer
								s:= st__; 

								(*	Call `burn`	*)
								let (ret__2, st__2) = _burn (!s) in_msg.sender res in 
									match ret__2 with 
										| Some _ -> (
														// updated state after burning
														s:= st__2; 

														(*	Call `_bridgeOwner.transfer(msg.value)` is an external call
															to the trusted account/contract `_bridgeOwner` thus it can
															be assumed as true
														*)

														(* vi)  update state with the new event - emit  SentToChain(msg.sender, amount - fee,
																													block.chainid, destinationChainId, 
																													destinationToken); *)
														let events_length_old : nat = length (!s).events_ in
														s := 	{!s with events_ = SentToChain in_msg.sender (FStar.UInt256.sub amount fee) 
																(!s).block.chainid destinationChainId destinationToken :: (!s).events_};
														
														 // verify that the events_ list has grown - event has been emitted
														let events_length_new : nat = length (!s).events_ in 
														let _ = assert(events_length_old < events_length_new) in 

														// return updated state
														(Some (), !s)
													)

										| _ -> raise Solidity.SolidityBurnError		
								)
					| _     -> raise Solidity.SolidityTransferError
        with
            // if any other error occurs keep the old state (revert)
            _ -> (None, state)	