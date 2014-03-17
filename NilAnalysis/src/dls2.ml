open Cfg
open Cfg_printer
open Visitor
open Utils
open Cfg_refactor
open Cfg_printer.CodePrinter
open Printf
open Str
  
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
    (* if s <> "\n" then *)
    let fact =
      try meet_fact (StrMap.find s map) v
      with Not_found -> v
    in 
    StrMap.add s fact map	
    (* else map *)
       

  let update_IF s v map =
    let fact =
      try meet_fact_IF (StrMap.find s map) v
      with Not_found -> v
    in 
    StrMap.add s fact map	

      
  let join lst =		(*join receives a list of StrMap (String, fact) *) 
    (* print_string "joinnnnnnn \n" ; *)
   	(* if (List.length lst) > 1 then *)
      let map1 = (fun acc map -> StrMap.fold update_IF map acc) (List.nth lst 0) (List.nth lst 1) in
      let map2 = (fun acc map -> StrMap.fold update_IF map acc) (List.nth lst 1) (List.nth lst 0) in
      (fun acc map -> StrMap.fold update_IF map acc) map1 map2		(* now map1 and map2 are defined on the same set of variables *)
     (* else
      List.fold_left (fun acc map ->
        StrMap.fold update map acc) StrMap.empty lst    *)

 (*
  let rec update_lhs_orig fact map lhs = 
    let map = match lhs with
    | `ID_Var(`Var_Local, var) -> update var fact map
    | `ID_Var(`Var_Constant, const) -> update const fact map
    | #identifier -> map
    | `Tuple lst -> List.fold_left (update_lhs_orig fact) map lst
    | `Star (#lhs as l) -> print_string "asdasd\n"; update_lhs_orig fact map l
    in map *)




  (* VISITE *)

  let rec update_literal lit fact map =
    print_string "ALE update_literal:\n";
    match lit with 
      | `Lit_Array star_lst -> print_string "ALE star_list:\n"; 
                              (* qua ci vanno le robe del for tipo [[a,b][c,4]] *)
                              let map = List.fold_left (fun acc x -> update_star_expr x fact acc) map star_lst in map
                              (* update_star_expr_list star_lst fact map *)
      | `Lit_Hash pair_lst ->  print_string "ALE pair_list:\n"; 
                              let map = List.fold_left (fun acc (e1, e2) -> 
                                  let acc = update_expr e1 fact acc in
                                  update_expr e2 fact acc
                              ) map pair_lst in map
      | `Lit_Range(b, e1, e2) -> print_string "ALE lit_range:\n";
                                  let map = (update_expr e1 fact map) in
                                  let map = (update_expr e2 fact map) in
                                  map 
       |  _ -> print_string "ALE altro!!!\n"; map (* per esempio una stringa o cmq qualcosa che non analizzo *)

  and update_identifier id fact map = 
    print_string "ALE update_identifier:\n";
    match id with
      | `ID_Var(`Var_Local, var) -> print_string "ALE var local.\n"; update var fact map
      | `ID_Var(`Var_Constant, const) -> print_string "ALE var constant.\n"; update const fact map
      | `Tuple lst -> print_string "ALE tuple:\n"; List.fold_left (fun acc x -> update_expr x fact acc) map lst
      | _ ->  print_string "ALE qualcos'altro!!!\n"; map 

  and update_expr (e: expr) fact map =
    print_string "ALE update_expr:\n";
    match e with
      | #literal as l -> (update_literal l fact map)
      | #identifier as id -> (update_identifier id fact map)

  and update_lhs lhs fact map = 
    match lhs with
    | `ID_Var(`Var_Local, var) -> update var fact map
    | `ID_Var(`Var_Constant, const) -> update const fact map 
    (* identifier *)
    | #identifier as id -> (update_identifier id fact map)
    (* lhs tuple *)
    | `Tuple lhs_lst -> List.fold_left (fun acc x -> update_lhs x fact acc) map lhs_lst
    (* identifier star *)
    | `Star (#identifier as id) -> update_identifier id fact map

  and update_lhs_option lhs_o fact map =
    match lhs_o with
     | None -> map
     | Some lhs -> update_lhs lhs fact map;

  and update_expr_option expr_o fact map =
    match expr_o with 
      | None -> map
      | Some (`ID_Var(_,_) as var) -> update_identifier var fact map
      | _ -> map


  and update_star_expr star fact map = 
    print_string "ALE update_star_expr:\n";
    match star with
      | #expr as e -> update_expr e fact map
      | `Star e -> let map = (update_expr e fact map) in map


  and update_tuple_expr tup fact map =
    match tup with 
      | #expr as e -> (update_expr e fact map)
      | `Star (#expr as e) -> (update_expr e fact map)
      | `Tuple lst (* -> List.fold_left (fun acc x -> update_tuple_expr x fact acc) map lst *)
      | `Star (`Tuple lst) -> List.fold_left (fun acc x -> update_tuple_expr x fact acc) map lst

  and update_tuple_expr_option tup_o fact map =
    match tup_o with
      | None -> map
      | Some el -> update_tuple_expr el fact map

  let rec update_formal_param p fact map =
    match p with
        | `Formal_block_id(_,s) -> update s fact map
        | `Formal_star(s) -> update s fact map
        | `Formal_tuple(m) -> List.fold_left (fun acc x -> (update_formal_param x fact acc)) map m




  (* TRANSFER *)

  let rec transfer map stmt = 
    (* print_string "\nnuova chiamata a transfer:\n"; *)
    (* stmt.snode is the type of the stmt *)
    match stmt.snode with
    
    (* if stmt is an assign with right hand side not variable *)
    | Assign(lhs , #literal) 
    | Assign(lhs , `ID_True) 
    | Assign(lhs , `ID_False)
    | Assign(lhs , `ID_Nil) -> 
        (* print_string "ALE assign true, false, literal or null\n"; *)

        (* we analyse the left hand side and set it to dead *)
        update_lhs lhs Dead map

    (* if it is an assignment with a variable as rhs *)
    | Assign(lhs, (`ID_Var(_, _) as var)) -> 
        (* print_string "ALE assign id_var\n" ; *)

        (* we set the lhs to dead, and set the rhs variable to dead *)
        let map = update_lhs lhs Dead map in 
        update_expr var Live map
    (* if it is an assignment with a composite rhs *)   
    | Assign(lhs, (`Tuple(_) as tup)) -> 
        (* print_string "ALE assign tuple\n" ;  *)
        
        (* we set the lhs to dead, and analyse the rhs to set the variable that contains to dead *)
        let map = update_lhs lhs Dead map in
        update_tuple_expr tup Live map                                             

    (* if it is a MethodCall *)
    | MethodCall(lhs_o, {mc_target = target; mc_args = args} ) -> 
        (* print_string "MethodCall id_var\n"; *) 

        (* we set the lhs to dead *)
        let map = update_lhs_option lhs_o Dead map in
        (* we analyse the argoments of the function and set to live the variable *) 
        let map = List.fold_left (fun acc x -> update_star_expr x Live acc) map args in
        (* if present, the target of the function is set to live *)
        (* NOTE: classes in ruby are variables, so we don't care what is the target *)
        update_expr_option target Live map

    (* if it is a case in which there is only an expr to analyse *)
    | Expression(e)
    | If(e,_,_)
    | While(e, _) -> 
        (* print_string "while\n"; *)

        (* we set the expr to live because it is read *)
        update_expr e Live map

    (* if it is a for *)
    | For(p, e, _) -> 
        (* print_string "for preso param\n"; *)

        (* we set to dead all the formal fìparameter *)
        let map = List.fold_left(fun acc x -> update_formal_param x Dead acc) map p in 
        (* and to live the expression of the for *)
        update_expr e Live map
  
    
    (* if it a case stmt *)
    | Case(all) -> 
        (* print_string "case\n"; print_string ("vediamo-> "^(to_string map)); print_string "\n"; *)

        (* we set to live all the guards (whens and case) *)
        let map = List.fold_left (fun acc (s, _) -> update_tuple_expr s Live acc) map all.case_whens in
        update_expr all.case_guard Live map

    (* if it is a case stmt *)
    | Yield(lhs_o ,args) -> 
        (* print_string "yield\n"; *)

        (* we set to live the values that the yield pass to the block *)
        let map = List.fold_left (fun acc x -> update_star_expr x Live acc) map args in
        (* and to dead the variable taht save the return of the yield *)
        update_lhs_option lhs_o Dead map

   (* if it is a return *)
   | Return(s)-> 
        (* print_string "return\n"; *)

        (* we set to live the value return because it is readed *)
        update_tuple_expr_option s Live map


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

    (* all other cases are ignored *)
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
    
  let rec update_lhs_orig fact map lhs = match lhs with
    | `ID_Var(`Var_Local, var) -> update var fact map
    | `ID_Var(`Var_Constant, const) -> update const fact map
    | #identifier -> map
    | `Tuple lst -> List.fold_left (update_lhs_orig MaybeNil) map lst
    | `Star (#lhs as l) -> update_lhs_orig NonNil map l
      
  let transfer map stmt = match stmt.snode with
    | Assign(lhs , #literal) | Assign(lhs , `ID_True) | Assign(lhs , `ID_False) -> update_lhs_orig NonNil map lhs
    | Assign(lhs , `ID_Nil) -> update_lhs_orig MaybeNil map lhs
    | Assign(lhs, `ID_Var(`Var_Local, rvar)) -> update_lhs_orig (StrMap.find rvar map) map lhs
    | Assign(lhs, `ID_Var(`Var_Constant, rconst)) -> update_lhs_orig (StrMap.find rconst map) map lhs
    | MethodCall(lhs_o, {mc_target=Some (`ID_Var(`Var_Local, targ))}) ->
     	let map = match lhs_o with
        | None -> map
        | Some lhs -> update_lhs_orig MaybeNil map lhs (* to be updated! *)
      in
      map (*get_fact targ map StrMap.add targ NonNil map*)
    | Class(Some lhs, _ , _ ) 
    | Module(Some lhs, _ , _ )
    | MethodCall(Some lhs, _ )
    | Yield(Some lhs, _ )
    | Assign(lhs, _ ) -> update_lhs_orig MaybeNil map lhs
      
    | _ -> map             
end






































(* INIZIO MODULO LIVENESS *)

module Liveness = Dataflow.Backwards(LivenessAnalysis)

    (* INIZIOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO *)
let justif input =
  let lines = split (regexp_string "\n") input in
  let fields_l = List.map (split (regexp_string "$")) lines in
  let fields_l = List.map Array.of_list fields_l in
  let n = (* number of columns *)
    List.fold_left
      (fun n fields -> max n (Array.length fields))
      0 fields_l
  in
  let pads = Array.make n 0 in
  List.iter (
    (* calculate the max padding for each column *)
    Array.iteri
      (fun i word -> pads.(i) <- max pads.(i) (String.length word))
  ) fields_l;

  let print f =
    List.iter (fun fields ->
      Array.iteri (fun i word ->
        f word (pads.(i) - (String.length word))
      ) fields;
      print_newline()
    ) fields_l;
  in

  (* left column-aligned output *)
  print (fun word pad ->
    let spaces = String.make pad ' ' in
    Printf.printf "%s%s " word spaces)

    (* FINEEEEEEEEEEEEEEEEEEEEEEEE *)

		let print_pos node pos =
    print_string "[WARNING]: Dead var: \n in method call "; print_stmt stdout node; 
    Printf.printf " at %s:%d \n"
      pos.Lexing.pos_fname pos.Lexing.pos_lnum; 
    flush_all () 
  (* Printf.printf "[WARNING]: MaybeNil dereference in %s at line %d \n" *)
  (* pos.Lexing.pos_fname pos.Lexing.pos_lnum; *)
  (* flush_all () *)


    let rec get_for_strings l =
    List.fold_left ( fun acc el ->
      match el with
        | `Formal_block_id(_,s) -> s :: acc
        | `Formal_star(s) -> s :: acc
        | `Formal_tuple(m) -> get_for_strings m
    ) [] l


    (* return a string of indentation *)
    let rec get_indent_string level = 
          match level with
            | 0 -> ""
            | _ -> "   "^(get_indent_string (level-1))

 
  (* return the string representing the live variable in the map *)
  let print_row_nostmt map =
     match (StrMap.is_empty map) with
      (* if the map is empty return the "end line" only *)
      | true -> "$|\n"
      (* otherwise iterate all the entry of the map and print only the live variables *)
      | false -> let cell = ref "" in 
                    StrMap.iter (
                     fun k w -> 
                      match w with
                        | LivenessAnalysis.Dead -> cell := !cell(* ^k^"_morto, " *)
                        | LivenessAnalysis.Live -> cell := !cell^k^", "
                    ) map; !cell^"$|\n"


      

    (* return the string of the analysis result in this format: *)
    (* (line_number_into_code)$|$line of code$|$live variable in this row$|$\n *)
    let rec print_var_table stmt out_tbl level =
      match stmt.snode with
      | Seq(list) ->
          let cell = ref "" in
          List.iter( fun x -> 
                      cell:= !cell^(print_var_table x out_tbl level)) list;
          !cell
      | While(g, b) ->
          let cell = ref "" in
          cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"while "^(string_of_expr g)^"$|$";
          cell:= !cell^(print_row_nostmt (Hashtbl.find out_tbl stmt));
          cell:= !cell^(print_var_table b out_tbl (level+1));
          cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"end$|$$|\n";
          !cell

      | If(g, t, f) ->

        let cell = ref "" in
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"if "^(string_of_expr g)^" then $|$";
        cell:= !cell^(print_row_nostmt (Hashtbl.find out_tbl stmt));
        cell:= !cell^(print_var_table t out_tbl (level+1));
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"else$|$$|\n";
        cell:= !cell^(print_var_table f out_tbl (level+1));
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"end$|$$|\n";
        !cell

      | For(p,g,b) ->
        let cell = ref "" in
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"for "^(String.concat " " (get_for_strings p))^" in "^(string_of_expr g)^" do$|$";
        cell:= !cell^(print_row_nostmt (Hashtbl.find out_tbl stmt));
        cell:= !cell^(print_var_table b out_tbl (level+1));
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"end$|$$|\n";
        !cell

      | Case (b) ->
        let cell = ref "" in
        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"case "^(string_of_expr b.case_guard)^"$|$";
        cell:= !cell^(print_row_nostmt (Hashtbl.find out_tbl stmt));
        let whens = b.case_whens in
        (* st will contain all the stmt in all the when's clauses *)
        List.iter(fun (e,s) -> 
                  (* cell := (fun num ->
                      match num with
                        | 0 -> !cell^""
                        | _ -> !cell^"  "^ ) 1; *)

                  cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"when "^(string_of_tuple_expr e)^" then$|$";
                  (* se si vuole la tabella anche del when usare la riga sotto *)
                  cell := !cell^(print_row_nostmt (StrMap.add (string_of_tuple_expr e) LivenessAnalysis.Live (Hashtbl.find out_tbl s)));
                  (* altrimenti usare quest'altra *)
                  (* cell := !cell^"$|\n"; *)
                  
                  (* ricorsiva per gli statement dentro al when *)
									cell := !cell^(print_var_table s out_tbl (level+1));
        ) whens;

        cell:= (fun x -> match x with
                | None -> !cell
                | Some s -> 
									cell := !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"else$|$"; 
                  (* se si vuole la tabella anche del'else usare la riga sotto *)
                  cell := !cell^(print_row_nostmt (Hashtbl.find out_tbl s));
                  (* altrimenti usare quest'altra *)
                  (* cell := !cell^"$|\n"; *)

                  (* ricorsiva per gli statement dentro all'else *)
									!cell^(print_var_table s out_tbl (level+1))
									) b.case_else; 

        cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^"end$|$$|\n";
        !cell

      | Method (_) -> ""

      | MethodCall(lhs_o, {mc_target = target; mc_args = args; mc_msg = msg}) ->
          let cell = ref "" in
          cell := !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level);
          cell := (fun x -> match x with
                    | None -> !cell
                    | Some lhs ->  !cell^(string_of_lhs lhs)^" = ") lhs_o;
          cell := (fun x -> match x with
                    | None -> !cell
                    | Some e ->  !cell^(string_of_expr e)^".") target;
          cell := !cell^(string_of_msg_id msg)^"(";
          let l = List.fold_right (fun x acc -> (string_of_star_expr x)::acc) args []  in
          cell := !cell^(String.concat ", " l);
          cell := !cell^")$|$"^(print_row_nostmt (Hashtbl.find out_tbl stmt));
          !cell (* ^(print_var_table stmt out_tbl (level+1)) *)

      

      | _ ->  let cell = ref "" in
          cell:= !cell^"("^(string_of_int(stmt.pos.Lexing.pos_lnum))^")$|$"^(get_indent_string level)^(string_of_cfg stmt)^"$|$"^(print_row_nostmt (Hashtbl.find out_tbl stmt));
          !cell
                

      
  let refactor targ node =
    let nodee = freparse ~env:node.lexical_locals
      "unless %a.nil? then %a end" format_expr targ format_stmt node
    in ChangeTo nodee
      
  let print_warning node =
    print_pos node node.pos;
  (* print_stmt stdout node *)


    (* ELIMINARE (NO, quando abbiamo provato non andava più) *)
  (*
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
  
  *)


  (* CREDO CHE NON LA USIAMO PIU' *)
  (*
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
   *)
;;





(* from a stmt, visits all the successors and save all the stmt in a list and return it *)
let rec acc_stmt todo visited =
  StmtSet.fold (fun stmt acc ->
      match StmtSet.exists (fun x -> 
            (* checks if the stmt exists in the list *)
            (string_of_cfg x) = (string_of_cfg stmt)
          ) acc with
      (* if present, do nothing and return the list inaletate *)
      | true -> visited
      (* if not present, add it to the list and analyse the succerssors with a recursive call *)
      | false -> acc_stmt stmt.succs (StmtSet.add stmt acc)
  ) todo visited


(* find the method def stmt and return a list of all the method def stmt found *)
(* note: the list is in reverse order *)
let find_def stmt =
  (* do the fold on the list of all the stmt in the program to find the method def *)
  StmtSet.fold (fun x acc -> 
                        match x.snode with
                        (* if the stmt is a method def insert it in head of the list *)
                        | Method(_,_, s) -> print_stmt stdout s; s::acc
                        (* otherwise the list remains the same *)
                        | _ -> acc
                ) (acc_stmt (StmtSet.add stmt StmtSet.empty) StmtSet.empty) []



(* MAIN!!!! (starts from here) *)
let main fname =
  (* read the ruby program in input *)
  let loader = File_loader.create File_loader.EmptyCfg [] in
  let s = File_loader.load_file loader fname in
  (* compute the cfg of the program *)
  let () = compute_cfg s in
  let () = compute_cfg_locals s in
  (* print the program tranformed in RIL code *)
  print_string "RIL transformed code: \n"; 
  print_stmt stdout s; 
   
  print_string "\n---------------------------------------------\n\n";

  (* print_string "\n STAMPA STRANAANANANANANNANANNANA \n \n"; *)

  (* find the Method definition statement, because we perform the analysis separately on them *)
  let list_def = find_def s in
  (* for every def found we do the analysis and print the result *)
    List.iter (fun x -> let o, i = Liveness.fixpoint x in
                    print_string "Live In Variables Table of Method Definition: \n \n";
                    justif (print_var_table x i 0); 
                    print_string "--------------------------------------------\n\n";  
                    print_string "Live Out Variables Table of Method Definition: \n \n";
                    justif (print_var_table x o 0);
                    print_string "--------------------------------------------\n\n";  
  ) list_def;

  (* do the analysis on the main program ignorind the method definition analysed yet *)
  let ofs, ifs = Liveness.fixpoint s in
  (* print the raw results *)
  (* print_string "-------------------------------------------\n"; 
  print_string "ifs content: \n"; 
  print_hash ifs; 
  print_string "-------------------------------------------\n"; 
  print_string "ofs content: \n"; 
  print_hash ofs; 
  *)
  (* print the results with the code *)
  print_string "--------------------------------------------\n\n";  
  print_string "Live In Variables Table: \n \n";
  justif (print_var_table s ifs 0);
  print_string "--------------------------------------------\n\n";  
  print_string "Live Out Variables Table: \n \n";
  justif (print_var_table s ofs 0);

  (* let sn = ( new analizeLivenes ifs :> cfg_visitor ) in
  let _ = visit_stmt (sn) s in *)
  (* print_string "Transformed code: \n"; *)
  (* CodePrinter.print_stmt stdout ss *)
  (* print_string "--------------------------------------------\n"; *)
  (* print_string "Output code: \n"; *)
  (* ErrorPrinter.print_stmt stdout ss *)
  Printf.printf("\n---------------------------------------------\n");
  print_endline "Liveness analysis complete.\n"

    
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
    
    
(* NOTA: print_hash della nilness 
         SERVE ANCORA QUA SOTTO? *)
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

