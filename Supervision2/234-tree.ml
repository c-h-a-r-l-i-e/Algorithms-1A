datatype node = Lf | Br of int list * node list | Explosion of int * node * node;

	
(*This will only ever run on the bottom row*)
fun insertBase (Br(keys, children)) value = if length(keys) < 3 
	then if value < List.nth(keys, 0) then Br([value] @ keys, children @ [Lf])
		else if length(keys) = 1 orelse value < List.nth(keys, 1) then Br([hd keys] @ [value] @ (tl keys), children @ [Lf])
			else  Br(keys @ [value], children @ [Lf])
	else if value < List.nth(keys, 1) then Explosion(List.nth(keys, 1), insertBase (Br([hd keys], [Lf, Lf])) value, (Br(List.drop(keys, 2), [Lf, Lf])))
		else Explosion(List.nth(keys, 1), (Br([hd keys], [Lf, Lf])), insertBase (Br(List.drop(keys, 2), [Lf, Lf])) value);
		
(*Takes a child node, the parent node and a position in which the child should go. Also deals with explosions*)
fun replace (Br(cKeys, cChildren)) (Br(pKeys, pChildren)) pos = Br(pKeys, List.take(pChildren, pos) @ [(Br(cKeys, cChildren))] @ List.drop(pChildren, pos + 1)) (*Merge new child into correct position*)
  | replace (Explosion(value, lt, rt)) (Br(keys, children)) pos = 
	if length(keys) < 3 then (Br(List.take(keys, pos) @ [value] @ List.drop(keys, pos), List.take(children, pos) @ [lt, rt] @ List.drop(children, pos + 1))) (*Place the exploded nodes in the correct position*)
		else if pos = 0 then Explosion(List.nth(keys, 1), (Br([value, hd keys], [lt, rt, List.nth(children, 1)])), (Br(List.drop(keys, 2), List.drop(children, 2))))
		else if pos = 1 then Explosion(List.nth(keys, 1), (Br([hd keys, value], [hd children, lt, rt])), (Br(List.drop(keys, 2), List.drop(children, 2))))
		else if pos = 2 then Explosion(List.nth(keys, 1), (Br([hd keys], List.take(children, 2))), (Br([value] @ List.drop(keys, 3), [lt, rt] @ List.drop(children, 3))))
		else Explosion(List.nth(keys, 1), (Br([hd keys], List.take(children, 2))), (Br([List.nth(keys, 2), value], [List.nth(children, 2), lt, rt])));
		

		
fun insertExplodes (Br(keys, children)) value = if hd children = Lf then insertBase (Br(keys, children)) value
	else if value < List.nth(keys, 0) then replace (insertExplodes (List.nth(children, 0)) value) (Br(keys, children)) 0
		else if length(keys) = 1 orelse value < List.nth(keys, 1) then replace (insertExplodes (List.nth(children, 1)) value) (Br(keys, children)) 1
			else if length(keys) = 2 orelse value < List.nth(keys, 2) then replace (insertExplodes (List.nth(children, 2)) value) (Br(keys, children)) 2
				else replace (insertExplodes (List.nth(children, 3)) value) (Br(keys, children)) 3;

				
fun insert tree value = let fun unexplode (Explosion(value, lt, rt)) = Br([value], [lt, rt])
											  | unexplode branch = branch
	in unexplode (insertExplodes tree value) end;
	
(*Failed delete codes:
0 -- node not in tree
1 -- node only has one key*)

exception FailedDelete of int;

exception FoundNode of int;

fun isBase (Br(keys, Lf::_)) = true
  | isBase (Br(keys, children)) = false;

	
fun deleteBase (Br(keys, children)) pos = if length(keys) > 1 then Br(List.take(keys, pos) @ List.drop(keys, pos + 1), List.drop(children, 1))
	(*If only one key in the node*)
	else raise FailedDelete(1);
	
fun getChildren (Br(keys, children)) = children;
fun getKeys (Br(keys, children)) = keys;


fun getSuccessor (Br(keys, Lf::xs)) pos = List.nth(keys, 0)
  | getSuccessor (Br(keys, children)) pos = getSuccessor (List.nth(children, pos + 1)) 0;
	
fun findAndDeleteBase Lf key = raise FailedDelete(0)
  | findAndDeleteBase (Br(keys, children)) key = if key < List.nth(keys, 0) then Br(keys, [findAndDeleteBase (List.nth(children, 0)) key] @ (List.drop(children, 1)))
		else if key = List.nth(keys, 0) then deleteBase (Br(keys, children)) 0
		else if length(keys) < 2 orelse key < List.nth(keys, 1) then Br(keys, (List.take(children, 1) @ [findAndDeleteBase (List.nth(children, 1)) key] @ (List.drop(children, 2))))
		else if key = List.nth(keys, 1) then deleteBase (Br(keys, children)) 0
		else if length(keys) < 3 orelse key < List.nth(keys, 2) then Br(keys, (List.take(children, 2) @ [findAndDeleteBase (List.nth(children, 2)) key] @ (List.drop(children, 3))))
		else if key = List.nth(keys, 2) then deleteBase (Br(keys, children)) 0
		else Br(keys, (List.take(children, 3) @ [findAndDeleteBase (List.nth(children, 3)) key]))			
			
			

fun deleteNotBase (Br(keys, children)) pos = let val successor = getSuccessor (Br(keys, children)) pos in Br(List.take(keys, pos) @ [successor] @ List.drop(keys, pos + 1),
	List.take(children, pos + 1) @ [findAndDeleteBase (List.nth(children, pos + 1)) successor] @ List.drop(children, pos + 2)) end;
	

(*pos gives the position of the child to delete from, keypos the position of the key to delete within the child*)
fun deleteGeneral (Br(keys, children)) pos keypos = if isBase(List.nth(children, pos)) 
	then (Br(keys, List.take(children, pos) @ [deleteBase (List.nth(children, pos)) keypos] @ List.drop(children, pos + 1)) handle FailedDelete 1 => 
		if length(keys) > 1
			then replace (insertExplodes (List.nth(children, (if pos = 0 then 1 else pos - 1))) (List.nth(keys, (if pos = 0 then 1 else pos - 1)))) 
				(Br((if pos = 0 then List.drop(keys, 1) else (List.take(keys, pos - 1) @ List.drop(keys, pos))), List.take(children, pos) @ List.drop(children, pos + 1))) 
					(if pos = 0 then 1 else (pos - 1))
			else Lf) (*TODO: Case where child is now empty and parent only has one node*)
	else (Br(keys, List.take(children, pos) @ [deleteNotBase (List.nth(children, pos)) keypos] @ List.drop(children, pos + 1)));

	
(*Recurses down and then calls deleteGeneral from the parent of the child containing the node we want to delete*)
fun delete Lf key = raise FailedDelete(0)
  | delete (Br(keys, children)) key = (*think abt case where deleting from root*) if key < List.nth(keys, 0) then Br(keys, [delete (List.nth(children, 0)) key] @ (List.drop(children, 1)))
			handle FoundNode pos => deleteGeneral (Br(keys, children)) 0 pos
		else if key = List.nth(keys, 0) then raise FoundNode(0)
		else if length(keys) < 2 orelse key < List.nth(keys, 1) then Br(keys, (List.take(children, 1) @ [delete (List.nth(children, 1)) key] @ (List.drop(children, 2))))
			handle FoundNode pos => deleteGeneral (Br(keys, children)) 1 pos
		else if key = List.nth(keys, 1) then raise FoundNode(1)
		else if length(keys) < 3 orelse key < List.nth(keys, 2) then Br(keys, (List.take(children, 2) @ [delete (List.nth(children, 2)) key] @ (List.drop(children, 3))))
			handle FoundNode pos => deleteGeneral (Br(keys, children)) 2 pos
		else if key = List.nth(keys, 2) then raise FoundNode(2)
		else Br(keys, (List.take(children, 3) @ [delete (List.nth(children, 3)) key]))
			handle FoundNode pos => deleteGeneral (Br(keys, children)) 3 pos;