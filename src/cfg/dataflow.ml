
open Printf
open Cfg
open Cfg_printer
open Cfg_refactor
open Cfg_printer.CodePrinter
open Visitor
open Utils

let rec exists_fp visited stmt exits =
	if StmtSet.is_empty stmt.succs
	then StmtSet.add stmt exits
	else
		let todo = StmtSet.diff stmt.succs visited in
		let visited' = StmtSet.union visited todo in
		StmtSet.fold
			(fun stmt exits ->
						exists_fp
							visited'
							stmt
							exits
			) todo exits

let exits stmt = exists_fp StmtSet.empty stmt StmtSet.empty

module type DataFlowProblem =
sig
	type t
	val empty : t
	val eq : t -> t -> bool
	val to_string : t -> string
	
	val transfer : t -> stmt -> t
	val join : t list -> t
end

module Forwards(DFP : DataFlowProblem) = struct

	let print_hash ifs = 
            Hashtbl.iter (fun k v -> 
                (*print_string "Statement: \n";*)
                print_string "\n";
                print_stmt stdout k;
                print_string(" ->  ");
                    if ((StrMap.is_empty v) == false) then
                        StrMap.iter (
                                fun k w -> 
                                        print_string "(";
                                        print_string k;
                                        print_string ", ";
                                        print_string (DFP.to_string w)
                        ) v 
                    else
                        print_string "\n";
            ) ifs
            
    let print_map v =  StrMap.iter (
                                fun k w -> 
                                        print_string "(";
                                        print_string k;
                                        print_string ", ";
                                        print_string (DFP.to_string w)
                        ) v 
	

	let rec super_fixpoint stmt in_tbl out_tbl =
		match stmt.snode with
			| Seq(list) -> print_string "SEQ\n";print_stmt stdout stmt;
				let ifacts = ref (Hashtbl.find in_tbl stmt) in
				let newfacts = ref !ifacts in
  				List.iter (fun x -> 
  					Hashtbl.replace in_tbl x !ifacts;
  					newfacts := super_fixpoint x in_tbl out_tbl;
  					Hashtbl.replace out_tbl x !newfacts;
  					ifacts := !newfacts
  					) list;
				!newfacts
			| _ ->  print_string "OTHER\n";print_stmt stdout stmt;
				let ifacts = ref (Hashtbl.find in_tbl stmt) in
					DFP.transfer !ifacts stmt

	let fixpoint stmt =
		let in_tbl = Hashtbl.create 127 in
		let out_tbl = Hashtbl.create 127 in
			Hashtbl.replace in_tbl stmt DFP.empty;
			let newfacts = super_fixpoint stmt in_tbl out_tbl in
				Hashtbl.replace out_tbl stmt newfacts;
		in_tbl, out_tbl
			
(*		let fixpoint stmt =
		let in_tbl = Hashtbl.create 127 in
		let out_tbl = Hashtbl.create 127 in
		let q = Queue.create () in
		Queue.push stmt q;
		Hashtbl.add in_tbl stmt DFP.empty;
		while not (Queue.is_empty q) do
			print_string "####################################\n";
			let stmt = Queue.pop q in
			print_string "STMT:\n";print_stmt stdout stmt;
			print_string "STAMPA LISTA @@@@@@@@@@@@@@@@@@@@@@@@@@\n";
			List.iter (fun x -> print_stmt stdout x;print_string "\n";) stmt.succl;
			print_string "PREDS:\n";
			let in_list =
				StmtSet.fold
					(fun pred acc -> print_stmt stdout pred;print_string "---\n";
								try (Hashtbl.find out_tbl pred) :: acc
								with Not_found ->
										Hashtbl.add out_tbl pred DFP.empty;
										DFP.empty :: acc
					) stmt.preds []
			in
			print_string "IN_LIST:\n";
			List.iter (fun m -> print_string (DFP.to_string m); print_string "\n"; ) in_list;
	(*		let in_facts = match stmt.snode with
				| While(_,_) -> DFP.join (List.tl in_list)
				| _ -> DFP.join in_list
			in *)
			
			let in_facts = DFP.join in_list in
			print_string "IN_FACTS\n";
			print_string (DFP.to_string in_facts);print_string "\n";
			
			let () = Hashtbl.replace in_tbl stmt in_facts in
			let new_facts = DFP.transfer in_facts stmt in
			print_string "NEW_FACTS\n";
			print_string (DFP.to_string new_facts);print_string "\n";
			try
				print_string "SUCCS:\n";
				let old_facts = Hashtbl.find out_tbl stmt in
				if DFP.eq old_facts new_facts
				then ()
				else begin
					StmtSet.iter (fun x -> print_stmt stdout x;print_string "------------------\n";Queue.push x q) stmt.succs;
					Hashtbl.replace out_tbl stmt new_facts
				end
			with Not_found ->
					StmtSet.iter (fun x -> print_stmt stdout x;print_string "------------------\n";Queue.push x q) stmt.succs;
					Hashtbl.replace out_tbl stmt new_facts
		done;
		in_tbl, out_tbl
		
		*)
	
end

module Backwards(DFP : DataFlowProblem) = struct
	
	let fixpoint stmt =
		let in_tbl = Hashtbl.create 127 in
		let out_tbl = Hashtbl.create 127 in
		let q = Queue.create () in
		StmtSet.iter
			(fun x ->
						Queue.push x q;
						Hashtbl.add in_tbl x DFP.empty
			) (exits stmt);
		while not (Queue.is_empty q) do
			let stmt = Queue.pop q in
			let in_list =
				StmtSet.fold
					(fun stmt acc ->
								try (Hashtbl.find out_tbl stmt) :: acc
								with Not_found ->
										Hashtbl.add out_tbl stmt DFP.empty;
										DFP.empty :: acc
					) stmt.succs []
			in
			let in_facts = DFP.join in_list in
			let () = Hashtbl.replace in_tbl stmt in_facts in
			let new_facts = DFP.transfer in_facts stmt in
			try
				let old_facts = Hashtbl.find out_tbl stmt in
				if DFP.eq old_facts new_facts
				then ()
				else begin
					StmtSet.iter (fun x -> Queue.push x q) stmt.preds;
					Hashtbl.replace out_tbl stmt new_facts
				end
			with Not_found ->
					StmtSet.iter (fun x -> Queue.push x q) stmt.preds;
					Hashtbl.replace out_tbl stmt new_facts
		done;
		in_tbl, out_tbl
	
end

module AndOr = struct
	type disj = [ `Method of string | `Or of disj * disj ]
	
	type cnf = [ disj | `And of t * t ]
	
	type any = [
		| `Method of string
		| `And of any * any
		| `Or of any * any
		]
	
end

module EarlyCast = struct
	open Cfg_printer.CodePrinter
	
	type t = StrSet.t StrMap.t
	
	let empty = StrMap.empty
	let eq t1 t2 = (StrMap.compare StrSet.compare t1 t2) = 0
	
	let to_string t =
		StrMap.fold
			(fun targ set acc ->
						StrSet.fold
							(fun msg acc ->
										(Printf.sprintf "[%s => %s], " targ msg) ^ acc
							) set acc
			) t ""
	
	let join l = 
		List.fold_left
			(fun acc env ->
						StrMap.fold
							(fun k v acc ->
										try
											let v' = StrMap.find k acc in
											StrMap.add k (StrSet.union v v') acc
										with Not_found ->
												StrMap.add k v acc
							) env acc
			) empty l
	
	
	let update t msg targ =
		try StrMap.add targ (StrSet.add msg (StrMap.find targ t)) t
		with Not_found -> StrMap.add targ (StrSet.singleton msg) t
	
	let transfer t s = match s.snode with
		| MethodCall(_, { mc_target = None }) -> (*assert false*)t
		| MethodCall(_, { mc_target = Some #literal }) -> (*assert false*)t
		| MethodCall(_, ({ mc_target = Some (#identifier as targ) } as mc)) ->
				let msg_str = format_to_string format_msg_id mc.mc_msg in
				let targ_str = format_to_string format_identifier targ in
				update t msg_str targ_str
		
		| Return(tuple_opt) -> t
		| Yield(lhso, args) -> t
		
		| Assign((#identifier as lhs), (#expr_ as rhs)) ->
				ignore(lhs, rhs); t
		
		| Assign(`Star _, _ ) -> (* assert false *) t
		| Assign(_, `Star _) -> (* assert false *) t
		| Assign(`Tuple _, _) -> (* assert false *) t
		| Assign(_, `Tuple _) -> (* assert false *) t
		
		| Undef _ -> Log.fixme "dataflow trasfer: undef"; t
		
		| Break _
		| Redo
		| Retry
		| Next _
		| Defined _
		| Seq _
		| Alias _
		| If _
		| Case _
		| While _
		| For _
		| Expression _
		| Module _
		| Method _
		| Class _
		| ExnBlock _
		| Begin _
		| End _ -> t
	
end

module EarlyCastDF = Backwards(EarlyCast)

module DataTypeFlow = struct
	
	type t = int
	
	let empty = 0
	let eq t1 t2 = t1 = t2
	
	let to_string t = string_of_int t
	
	let transfer t stmt =
		printf "xfer: %s\n" (format_to_string Cfg_printer.CodePrinter.format_stmt stmt);
		t +1
	
	let join ins = List.fold_left (+) 0 ins
end

module DataTypeFlowDF = Forwards(DataTypeFlow)

