open Cfg
open Cfg_printer
open Visitor
open Utils
open Cfg_refactor
open Cfg_printer.CodePrinter
open Printf
  
(* INIZIO CONTRACT LIVENESS *)
module C = Cfg.Abbr

module LivenessAnalysis = struct

  type fact = Live | Dead
    
  let fact_to_s = function Live -> "Live" | Dead -> "Dead"
    
  let top = StrMap.empty
  type t = fact StrMap.t
  let empty = StrMap.empty
  let eq t1 t2 = StrMap.compare Pervasives.compare t1 t2 = 0 
  let to_string t = strmap_to_string fact_to_s t
    
				
  let meet_fact t1 t2 = match t1,t2 with	
    | _, Live ->  (* print_string "confronto \n"; *) Live			
    | _, Dead -> (* print_string "confronto \n"; *) Dead
      
  let meet_fact_IF t1 t2 = match t1,t2 with	
    | _, Live ->  (* print_string "confronto \n"; *) Live			
    | Live, _ -> (* print_string "confronto \n"; *) Live
    | Dead, Dead -> (* print_string "confronto \n"; *) Dead
      
  let update s v map =
    if s <> "\n" then
    let fact =
      try meet_fact (StrMap.find s map) v
      with Not_found -> v
    in 
    StrMap.add s fact map	
  else map
      
  let update_IF s v map =
    let fact =
      try meet_fact_IF (StrMap.find s map) v
      with Not_found -> v
    in 
    StrMap.add s fact map	
      
  let join lst =		(*join receives a list of StrMap (String, fact) *) 
    (* print_string "joinnnnnnn \n" ; *)
   	if (List.length lst) > 1 then
      let map1 = (fun acc map -> StrMap.fold update_IF map acc) (List.nth lst 0) (List.nth lst 1) in
      let map2 = (fun acc map -> StrMap.fold update_IF map acc) (List.nth lst 1) (List.nth lst 0) in
      (fun acc map -> StrMap.fold update_IF map acc) map1 map2		(* now map1 and map2 are defined on the same set of variables *)
    else
      List.fold_left (fun acc map ->
        StrMap.fold update map acc) StrMap.empty lst

  let rec get_for_strings l =
    List.fold_left ( fun acc el ->
      match el with
        | `Formal_block_id(_,s) -> s :: acc
        | `Formal_star(s) -> s :: acc
        | `Formal_tuple(m) -> get_for_strings m
    ) [] l
        
  let rec update_lhs fact map lhs = 
		let map = match lhs with
    | `ID_Var(`Var_Local, var) -> update var fact map
    | `ID_Var(`Var_Constant, const) -> update const fact map
    | #identifier -> map
    | `Tuple lst -> List.fold_left (update_lhs fact) map lst
    | `Star (#lhs as l) -> print_string "asdasd\n"; update_lhs fact map l
		in map

  let update_use lhs value map =
    let map = update_lhs Dead map lhs 
    in let map = update value Live map
  in map

 let rec aux e = match (e: expr) with
    | #literal -> print_string "lit\n"; "\n"
    | #identifier as id -> print_string "id\n" ;
      match id with
      | `ID_Var(`Var_Local, var) -> print_string "var local\n"; var
      | `ID_Var(`Var_Constant, const) -> print_string "var constant \n"; const
      | `Tuple lst -> print_string "tuple\n" ; aux lst
      | _ ->  print_string "qualcos'altro\n"; "\n"

 let rec vst_expr e = match e with
  | `Star el -> print_string "star\n"; vst_expr (el :> star_expr)
  | #expr as e -> print_string "expr\n";  

    match (e: expr) with
    | #literal -> print_string "lit\n"; "\n"
    | #identifier as id -> print_string "id\n" ;
      match id with
      | `ID_Var(`Var_Local, var) -> print_string "var local\n"; var
      | `ID_Var(`Var_Constant, const) -> print_string "var constant \n"; const
      | `Tuple lst -> print_string "tuple\n" ;"\n"
      | _ ->  print_string "qualcos'altro\n"; "\n"

  let rec match_tuple_expr map value = match value with
    | #expr as e-> print_string "expr tuple\n"; update (vst_expr (e:> star_expr)) Live map
    | `Star (#expr as e) -> print_string "star tuple\n"; update (aux e) Live map

    | `Tuple lst | `Star(`Tuple lst) -> print_string "star tuple tuple\n";
      let map = List.fold_left (match_tuple_expr ) map lst in map


  let rec vst_list_tuple list map = match list with
    | [] -> print_string "lista vuota\n"; map
    | head :: tail -> print_string "lista non vuota\n"; 
    let map = match_tuple_expr map head in
    let map = vst_list_tuple tail map 
        
      in map

  let rec visit_list list map = match list with
    | [] -> print_string "lista vuota\n"; map
    | head :: tail -> print_string "lista non vuota\n"; 
    let map = visit_list tail map in
        let map = update (vst_expr head) Live map
      in map

  let rec visit_for_param list map = match list with
    | [] -> print_string "lista vuota\n"; map
    | head :: tail -> print_string "lista non vuota\n"; 
      let map = visit_for_param tail map in
        let map = update head Dead map
      in map

  let rec multiple_join map list = match list with
  | [] -> map
  | head :: tail -> 
    let map = join map::head in 
      let map = multiple_join map tail 
    in map

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

  let tmp_fix stmt t =
    let in_tbl = Hashtbl.create 127 in
    let out_tbl = Hashtbl.create 127 in
    let q = Queue.create () in
    StmtSet.iter
      (fun x ->
            Queue.push x q;
            Hashtbl.add in_tbl x empty
      ) (exits stmt);
      
    while not (Queue.is_empty q) do
      let stmt = Queue.pop q in
      let in_list =
        StmtSet.fold
          (fun stmt acc ->
                try (Hashtbl.find out_tbl stmt) :: acc
                with Not_found ->
                    Hashtbl.add out_tbl stmt empty;
                    empty :: acc
          ) stmt.succs [] in
      let in_facts = join in_list in
      let () = Hashtbl.replace in_tbl stmt in_facts in
      let new_facts = t in_facts stmt in
        try
          let old_facts = Hashtbl.find out_tbl stmt in
          if eq old_facts new_facts
          then ()
          else begin
            StmtSet.iter (fun x -> Queue.push x q) stmt.preds;
            Hashtbl.replace out_tbl stmt new_facts
          end
        with Not_found ->
            StmtSet.iter (fun x -> Queue.push x q) stmt.preds;
            Hashtbl.replace out_tbl stmt new_facts
    done;

    out_tbl 

  let rec transfer map stmt = match stmt.snode with

    | Assign(lhs , #literal) | Assign(lhs , `ID_True) | Assign(lhs , `ID_False) -> print_string "true false literal\n"; update_lhs Dead map lhs
    | Assign(lhs , `ID_Nil) -> print_string "null\n"; update_lhs Dead map lhs
    | Assign(lhs, `ID_Var(`Var_Local, rvar)) ->  print_string "var\n"; update_use lhs rvar map
    | Assign(lhs, `ID_Var(`Var_Constant, rconst)) ->  print_string "constant\n"; update_use lhs rconst map
    | Assign(lhs, `Tuple s) -> print_string "tuple\n" ; 
      let map = update_lhs Dead map lhs in
        let map = vst_list_tuple s map 
      in map

    | MethodCall(lhs_o, {mc_target = Some (`ID_Var(`Var_Local, var) as target); mc_args = args} ) 
    | MethodCall(lhs_o, {mc_target = Some (`ID_Var(`Var_Constant, var) as target); mc_args = args} )-> 
			 print_string "MethodCall\n";

     let map =  visit_list args map in
      let map = match lhs_o with
				| None -> map
				| Some lhs -> update_lhs Dead map lhs;
				in let map = update_lhs Live map target 
			in map

    | MethodCall(lhs_o, {mc_args = args} ) ->
      
      let map =  visit_list args map in
        let map = match lhs_o with
        | None -> map
        | Some lhs -> update_lhs Dead map lhs;
      in map

    | While(`ID_Var(`Var_Local, rvar) , _) 
    | While(`ID_Var(`Var_Constant, rvar) , _) -> print_string "while\n"; update rvar Live map

    | For(p, e, _) -> print_string "for preso param\n"; 
    let map =
      let list = get_for_strings p in
        print_string (String.concat " " list); print_string "\n";
        visit_for_param list map
      in let l = ((e:> star_expr)::[]) in
      let map = visit_list l map
    in map
    
    | If(`ID_Var(`Var_Local, rvar) ,_,_) -> print_string "if\n"; update rvar Live map
    | If(`ID_Var(`Var_Constant, rvar) ,_,_) -> print_string "if\n"; update rvar Live map
    

    | Case(all) -> print_string "case\n"; print_string ("vediamo-> "^(to_string map)); print_string "\n";

          let whens = all.case_whens in
        (* st will contain all the stmt in all the when's clauses *)
          let cond = List.fold_left ( fun acc (s, _) -> (s :> tuple_expr)::acc ) [] whens in
          (* let stm = List.fold_left ( fun acc (_, s) -> s::acc ) [] whens in
          let map = List.fold_left (fun acc x -> Hashtbl.find (tmp_fix x (transfer)) x ) map stm in *)
          let map = vst_list_tuple cond map in
          let l = ((all.case_guard:> star_expr)::[]) in
          let map = visit_list l map

        in map

    | Yield(lhs_o ,args) -> print_string "yield\n";
      let map =  visit_list args map in
        let map = match lhs_o with
        | None -> map
        | Some lhs -> update_lhs Dead map lhs;
      in map

   | Return(s)-> print_string "return\n"; 
      let map = match s with
      | None -> map
      | Some el -> vst_list_tuple (el::[]) map
    in map

    | Expression(e) -> print_string "expression\n"; 
      let map = update (vst_expr (e :> star_expr)) Live map
        in map



    (*    ELIMINABILI 

    | Module(_,_,_)-> print_string "module\n"; map

    | Expression(_) -> print_string "expression\n"; map

    | Alias(_) -> print_string "alias\n"; map

    | Class(_,_,_)-> print_string "class\n"; map

    | Seq(_) -> print_string "seq\n"; map

    | Begin(_) -> print_string "begin\n"; map

    | End(_)-> print_string "end\n"; map 

    | ExnBlock(_)-> print_string "exnblock\n"; map

    | Method (_,_,_)-> print_string "method def\n"; map

    | Break(_) -> print_string "break niente \n"; map

*)
    (*| Break(`ID_Var(`Var_Local, rvar)) -> print_string "break\n"; update rvar Live map
    | Break(`ID_Var(`Var_Constant, rvar)) -> print_string "break\n"; update rvar Live map
*)

    | _ -> map 

end

(* FINE CONTRACT LIVENESS *)

module NilAnalysis = struct
  type fact = MaybeNil | NonNil
    
  let fact_to_s = function MaybeNil -> "MaybeNil" | NonNil -> "NonNil"
    
  let meet_fact_IF t1 t2 = match t1,t2 with
    | MaybeNil, _ 
    | _, MaybeNil -> MaybeNil
    | NonNil, NonNil -> NonNil
      
  let meet_fact t1 t2 = match t1,t2 with	
    | _, NonNil -> NonNil
    | _, MaybeNil -> MaybeNil
      
  let update s v map =
    let fact =
      try meet_fact (StrMap.find s map) v
      with Not_found -> v
    in
    StrMap.add s fact map (* this instruction returns a new map! it does not modify ifacts *)
      
  let updateIF s v map =
    let fact =
      try meet_fact_IF (StrMap.find s map) v
      with Not_found -> MaybeNil
    in 
    StrMap.add s fact map
      
  let join lst =		(*join receives a list of StrMap (String, fact) *) 	
   	if (List.length lst) > 1 then
      let map1 = (fun acc map -> StrMap.fold updateIF map acc) (List.nth lst 0) (List.nth lst 1) in
      let map2 = (fun acc map -> StrMap.fold updateIF map acc) (List.nth lst 1) (List.nth lst 0) in
      (fun acc map -> StrMap.fold updateIF map acc) map1 map2		(* now map1 and map2 are defined on the same set of variables *)
    else
      List.fold_left (fun acc map ->
        StrMap.fold update map acc) StrMap.empty lst
        
 	type t = fact StrMap.t
  let empty = StrMap.empty
  let eq t1 t2 = StrMap.compare Pervasives.compare t1 t2 = 0 
  let to_string t = strmap_to_string fact_to_s t
    
  let rec update_lhs fact map lhs = match lhs with
    | `ID_Var(`Var_Local, var) -> update var fact map
    | `ID_Var(`Var_Constant, const) -> update const fact map
    | #identifier -> map
    | `Tuple lst -> List.fold_left (update_lhs MaybeNil) map lst
    | `Star (#lhs as l) -> update_lhs NonNil map l
      
  let transfer map stmt = match stmt.snode with
    | Assign(lhs , #literal) | Assign(lhs , `ID_True) | Assign(lhs , `ID_False) -> update_lhs NonNil map lhs
    | Assign(lhs , `ID_Nil) -> update_lhs MaybeNil map lhs
    | Assign(lhs, `ID_Var(`Var_Local, rvar)) -> update_lhs (StrMap.find rvar map) map lhs
    | Assign(lhs, `ID_Var(`Var_Constant, rconst)) -> update_lhs (StrMap.find rconst map) map lhs
    | MethodCall(lhs_o, {mc_target=Some (`ID_Var(`Var_Local, targ))}) ->
     	let map = match lhs_o with
        | None -> map
        | Some lhs -> update_lhs MaybeNil map lhs (* to be updated! *)
      in
      map (*get_fact targ map StrMap.add targ NonNil map*)
    | Class(Some lhs, _ , _ ) 
    | Module(Some lhs, _ , _ )
    | MethodCall(Some lhs, _ )
    | Yield(Some lhs, _ )
    | Assign(lhs, _ ) -> update_lhs MaybeNil map lhs
      
    | _ -> map             
end

(* INIZIO MODULO LIVENESS *)

module Liveness = Dataflow.Backwards(LivenessAnalysis)
  
		let print_pos node pos =
    print_string "[WARNING]: Dead var: \n in method call "; print_stmt stdout node; 
    Printf.printf " at %s:%d \n"
      pos.Lexing.pos_fname pos.Lexing.pos_lnum; 
    flush_all () 
  (* Printf.printf "[WARNING]: MaybeNil dereference in %s at line %d \n" *)
  (* pos.Lexing.pos_fname pos.Lexing.pos_lnum; *)
  (* flush_all () *)
    let print_map v =  StrMap.iter (
      fun k w -> 
        print_string "(";
        print_string k;
        print_string ", ";
        print_string (LivenessAnalysis.to_string w)
      ) v 

    let rec get_for_strings l =
    List.fold_left ( fun acc el ->
      match el with
        | `Formal_block_id(_,s) -> s :: acc
        | `Formal_star(s) -> s :: acc
        | `Formal_tuple(m) -> get_for_strings m
    ) [] l

  let print_row_table k map =
    (* print_int stdout k; *)
    print_stmt stdout k;
    Printf.printf " %d - %d\n" k.pos.Lexing.pos_lnum k.sid;
    print_string "\n"
      (* print_string "-\n"*)

    let rec print_var_table stmt out_tbl =
      match stmt.snode with
      | Seq(list) ->
          List.iter( fun x -> 
                      print_var_table x out_tbl ) list
      | While(g, b) ->
          print_string "while \n"; 
          print_var_table b out_tbl; 
          print_string "end\n"

      | For(p,_,b) ->
          print_string "for "; 
          print_string (String.concat " " (get_for_strings p)); print_string "\n";
          print_var_table b out_tbl; 
          print_string "end\n"

      | _ -> print_row_table stmt (Hashtbl.find out_tbl stmt)

      (* let list_tbl = 
        Hashtbl.fold (fun k v acc -> k :: acc) out_tbl [] in

        let sorted = List.sort (fun x y -> Pervasives.compare x.pos y.pos ) list_tbl in
        List.iter (fun x -> match x.snode with
                            | Seq(_) -> print_string ""
                            | _ -> print_row_table x (Hashtbl.find out_tbl x)
        ) sorted *)

      
  let refactor targ node =
    let nodee = freparse ~env:node.lexical_locals
      "unless %a.nil? then %a end" format_expr targ format_stmt node
    in ChangeTo nodee
      
  let print_warning node =
    print_pos node node.pos;
  (* print_stmt stdout node *)


    
  class analizeLivenes ifs = object(s)		(* safeNil visitor *)
    inherit default_visitor as super
    val facts = ifs
      
    method visit_stmt node = match node.snode with 
      | Method(mname, args, body) -> 

        print_string "Method definition: \n";
        let in', out' = Liveness.fixpoint body in
        s#print_hash (in', out');
        print_string "\n--------------------------------------------\n";
        let me = {<facts = in'>} in
        let body' = visit_stmt (me:>cfg_visitor) body in
       	ChangeTo (update_stmt node (Method(mname, args, body')))
          
      | MethodCall( _ , {mc_target=(Some `ID_Self|None)}) -> SkipChildren
        
      | MethodCall( _ , {mc_target=Some (`ID_Var(`Var_Local, var) as targ)}) ->  print_string "testttttttt \n" ; print_string var ; print_string "\n"; print_stmt stdout node; print_string "\n";  
        begin try let map = Hashtbl.find facts node in 
          begin try match StrMap.find var map with
            | LivenessAnalysis.Dead -> print_warning node; refactor targ node
            | LivenessAnalysis.Live -> SkipChildren
                with Not_found ->  print_warning node; refactor targ node
          end
              with Not_found -> print_string "Assert false occurred in stmt: \n"; print_stmt stdout node; assert false
        end
        
      | MethodCall( _ , {mc_target=Some (`ID_Var(`Var_Constant, const) as targ)}) ->
        begin try let map = Hashtbl.find facts node in 
          begin try match StrMap.find const map with
            | LivenessAnalysis.Dead -> print_warning node; refactor targ node
            | LivenessAnalysis.Live -> SkipChildren
                with Not_found ->  print_warning node; refactor targ node
          end
              with Not_found -> print_string "Assert false occurred in stmt: \n"; print_stmt stdout node; assert false
        end
        
      | MethodCall(_, {mc_target=Some (#expr)}) -> SkipChildren  (* print_string "expr\n"; print_stmt stdout node; *)  (* (as targ) refactor targ node*)
      (* | MethodCall(_, _) -> SkipChildren *) 
        
      | _ -> super#visit_stmt node
        
    method print_hash (ifs, ofs) = 
      Hashtbl.iter (fun k v -> 
        (*print_string "Statement: \n";*)
        print_string "\n";
        print_stmt stdout k;
        print_string(" ->  ");
        if (StrMap.is_empty v == false) then
          StrMap.iter (
                       fun k w -> 
                         print_string "(";
                         print_string k;
                         print_string ", ";
                         match w with
                           | LivenessAnalysis.Dead -> print_string "Dead) "
                           | LivenessAnalysis.Live -> print_string "Live) "
                      ) v 
        else
          print_string "\n";
                   ) ifs
        
  end
  
  let print_hash _fs = 
    (*let num1 = Hashtbl.length ifs in
       let num2 = Hashtbl.length ofs in
       print_int(num1);print_string(" - ");print_int(num2);*)
    Hashtbl.iter (fun k v -> 
      (*print_string "Statement: \n";*)
      print_stmt stdout k;
      print_string(" ->  ");
      if (StrMap.is_empty v == false) then
       	StrMap.iter (
                     fun k w -> 
                       print_string "(";
                       print_string k;
                       print_string ", ";
                       match w with
                         | LivenessAnalysis.Dead -> print_string "Dead)\n "
                         | LivenessAnalysis.Live -> print_string "Live)\n "
                    ) v 
      else
        print_string "\n";
      
      print_string "\n";
      
                 ) _fs
;;

let main fname =
  let loader = File_loader.create File_loader.EmptyCfg [] in
  let s = File_loader.load_file loader fname in
  let () = compute_cfg s in
  let () = compute_cfg_locals s in
  print_string "RIL transformed code: \n"; 
  print_stmt stdout s; 
  
  (* ALE *)
  print_int s.pos.Lexing.pos_lnum;
  (**)
  
  print_string "\n---------------------------------------------\n\n";
  let ifs, ofs = Liveness.fixpoint s in
  print_string "-------------------------------------------\n"; 
  print_string "ifs content: \n"; 
  print_hash ifs; 
  print_string "-------------------------------------------\n"; 
  print_string "ofs content: \n"; 
  print_hash ofs; 
  print_string "--------------------------------------------\n";  
  print_var_table s ofs;
  (* let sn = ( new analizeLivenes ifs :> cfg_visitor ) in
  let _ = visit_stmt (sn) s in *)
  (* print_string "Transformed code: \n"; *)
  (* CodePrinter.print_stmt stdout ss *)
  (* print_string "--------------------------------------------\n"; *)
  (* print_string "Output code: \n"; *)
  (* ErrorPrinter.print_stmt stdout ss *)
  Printf.printf("\n---------------------------------------------\n");
  print_endline "Nilness analysis complete.\n"

    
let _ = 
  if (Array.length Sys.argv) != 2 
  then begin
    Printf.eprintf "Usage: print_cfg <ruby_file> \n";
    exit 1
  end;
  let fname = Sys.argv.(1) in
  main fname;
  ()
    
(* FINE MODULO LIVENESS *)
    
    
    
let print_hash _fs = 
  (*let num1 = Hashtbl.length ifs in
     let num2 = Hashtbl.length ofs in
     print_int(num1);print_string(" - ");print_int(num2);*)
  Hashtbl.iter (fun k v -> 
    (*print_string "Statement: \n";*)
    print_stmt stdout k;
    print_string(" ->  ");
    if (StrMap.is_empty v == false) then
      StrMap.iter (
                   fun k w -> 
                     print_string "(";
                     print_string k;
                     print_string ", ";
                     match w with
                       | NilAnalysis.MaybeNil -> print_string "MaybeNil)\n"
                       | NilAnalysis.NonNil -> print_string "NonNil)\n"
                  ) v 
    else
      print_string "\n";
				
    print_string "\n";
    
               ) _fs
;;

