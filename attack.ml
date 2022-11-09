(*#load "Unix.cma";;*)
(*#load "Unix";;*)
type transmit = R of int*int
               |K of int*int
               |Mm
	   			     |U
	 			       |M1 of transmit list;;

type comm = transmit list;;

let eg a b=
	match a with
		R(c,d) -> begin match b with R(e,f) -> c=e && d=f
				|_ -> false;end
		|K(c,d) -> begin match b with K(e,f) -> (c=e && d=f)||(c=f && d=e)
				|_ -> false;end
		|U -> begin match b with U -> true
				|_ -> false;end
		|M1(i) -> begin match b with M1(j) -> i=j
				|_ -> false;end
		|Mm -> begin match b with Mm -> true
				|_ -> false;end;;

let rec ajouttel d l=
	match d with
		[] -> l
		|[U] -> l
		|p::q -> match p with
				 M1(y) -> ajouttel q (enlevel y l)
				|_ -> ajouttel q (ajoutte p l)
and ajoutte d l=
	match l with
		[] -> [d]
		|[U] -> [d]
		|p::q -> match p with
				 M1(y) -> let l1=enleve d y in if List.length l1 > List.length y then p::(d::q) else
				 if l1 = [] then q else M1(l1)::q
				|_ -> d::l
and enlevel d l=
	match d with
		[] -> l
		|[U] -> l
		|p::q -> match p with
				 M1(y) -> enlevel q (ajouttel y l)
				|_ -> enlevel q (enleve p l)
and enleve d l=
	match l with
		[] -> [M1([d])]
		|[U] -> [M1([d])]
		|p::q -> match p with
				 M1(y) -> let l1=enleve d q in if List.length l1 > List.length q then M1(d::y)::q else p::l1
				|_ -> if p=d then q else p::(enleve d q);;

let fst3 (a,b,c)=a;;
let fsts3 (a,b,c) = (a,b);;
let thr3 (a,b,c) = c;;

let chiffre a=
	let s=String.make 1 a in
		("1"=s || "2"=s || "3"=s || "4"=s || "5"=s || "6"=s || "7"=s || "8"=s || "9"=s || "0"=s);;

let rec egU l=
	match l with
		[] -> false
		|p::q -> match p with
			U -> true
			| _ -> false;;

let cherche s=
	let i =ref 0 in begin
		while !i < (String.length s -2) && chiffre (s.[!i+1]) do
			incr i;
		done;
		(String.sub s 0 (!i+1),String.sub s (!i+1) (String.length s - !i-1));end;;

let cherche2 s=
	let (a,b)=cherche s in
		let (c,d)= cherche (String.sub b 1 (String.length b -1)) in (a,c,d);;

let decoupe s=
	let i =ref 0 in begin
	while !i < (String.length s -1) && chiffre (s.[!i+1]) do
		incr i;
	done;
	if !i = String.length s -1 then (int_of_string(s),"") else (int_of_string(String.sub s 0 (!i+1)),String.sub s (!i+1) (String.length s - !i-1));end;;

let cherch s =
	(* let i=ref (String.length s-1) and seul=ref true in *)
	let (a,b)=decoupe s in begin
		if b="" || b.[0]='K' || b.[0]='R' || b.[0]='-' then (a,1,b) else
		if String.length b=1 then failwith ("Problem with pasing (attack4)") else
		let (c,d)=decoupe (String.sub b 1 (String.length b -1)) in
			(a,c,d); end;;

let rec st2tr s=
	match s with
		"" -> []
		|s when s.[0] = 'K' ->let (a,b,c) = cherche2 (String.sub s 1 (String.length s -1)) in K(int_of_string(a),int_of_string(b))::(st2tr c)
		|s when s.[0] = 'R' ->let (a,b,c) = cherch (String.sub s 1 (String.length s -1)) in R(a,b)::(st2tr c)
		|s when s.[0] = '-' -> []
		|_ -> failwith (" I can't understand your protocol (attack4)");;

let conv (a,b,c)=(a,b,if c <>"" then st2tr(c) else [U]);;

let rec convl l=
	match l with
		[] -> []
		|p::q -> conv(p)::(convl q);;

let rec convpi l= (* Pi strings 2 list of R and K *)
	match l with
		[] -> []
		|p::q -> convl(p)::(convpi q);;

let rec term lpi i z= (* if we find (i,z) either s is empty so we add the next message, if it's not we remove s*)
	match lpi with
		[] -> [U]
		|[]::q -> term q i z
		|((a,b,s)::c)::q -> if a=i && b=z then begin if s=[U] then (thr3 (List.hd c)) else Mm::s; end
				  else term (c::q) i z;;

(* let rec term lpi i z= (* if we find (i,z) either s is empty so we add the next message, if it's not we remove s*)
match lpi with
[] -> [U]
|[]::q -> term q i z
|((a,b,s)::(d,e,t)::c)::q -> if a=i && b=z then s else if d=i && e=z then Mm::s else term (c::q) i z;;*)

let rec signe t= (* true iff + *)
	match t with
		[] -> failwith ("Empty ...")
		|p::q -> not(eg p Mm);;

let cltest a =
	if a=M1([]) then [] else [a];;

let rec cl l i=
	match l with
		[] -> []
		|p::q -> match p with
					M1(y) -> cltest(M1(cl y i))@(cl q i)
					|R(a,b) -> if a<>i then cl q i else p::(cl q i)
					|K(a,b) -> if a=i || b=i then p::(cl q i) else cl q i
					|_ -> p::(cl q i);;

let rec nunsterm t i= (* Remove the Mm *)
	match t with
		[] -> failwith ("This is empty... it should not ...")
		|p::q -> if eg p Mm then cl q i else cl t i;;

(* So that's the end of our typing tools *)

let rec pj j lpi=
	match lpi with
		[] -> failwith ("Sorry pi_j does not exist");
		|p::q -> if j =1 then p else pj (j-1) q;;

let rec che pi n = (* find the strand with Pi(n) *)
	match pi with
		[] -> (0,0)
		|p::q -> if n=1 then fsts3(p) else che q (n-1);;

let rec cherche a l n=
match l with
[] -> 0
|p::q -> if a=fsts3(p) then n else cherche a q (n+1);;

let izpj i z lpj= (* find (i,z) in lpj *)
	let n=cherche (i,z) lpj 1 in (n>0,n);;

let rec del a b l=
	match b with
		[] -> (b,a::l)
		|p::q -> if p=a then (q,l) else let (x,y)=del a q l in (p::x,y);;

let rec nettoiec a (b,l) = (* remove with a occurence in b *)
	match a with
		[] -> (l,b)
		|p::q -> nettoiec q (del p b l);;

let sansM1 a=
	match a with
		[] -> ([],[])
		|p::q ->begin match p with
			M1(i) -> (i,q)
			|_ -> ([],a);end;;

let sans_M1 a b= (* For simplicity, we transform all b.a^-1=d.c^-1 into c.b = d.a ...*)
	match a with
		[] -> sansM1 b
		|p::q ->begin let (x,y) = sansM1 b in match p with
			M1(i) -> (x@q,i@y)
			|_ -> (x@a,y);end;;

let rec sans_u l= (* Some transitions generate useless U values *)
	match l with
		[] -> []
		|p::q -> begin match p with U -> sans_u q
							|_ -> p::(sans_u q);end;;

let sansU l=
	if List.length l > 1 then sans_u l else l;;

let algo1 i j k (gg1,gg2) ta lpi= (* The core of the paper... *)
	let pij=pj j lpi and pik=pj k lpi and si=ref [] in
		let g1=ref gg1 and g2=ref gg2 in begin
			for z=1 to ta.(i) do
				let (a,x)=izpj i z pij and (b,y)=izpj i z pik and t=ref (term lpi i z) in begin
					if signe !t then begin
						if a && che pij x <> che pik x then begin g1:=ajouttel (nunsterm !t i) !g1; si:=(0,z,ajouttel gg1 (cl !t i))::(!si);end
						else if b && che pik y <> che pij y then begin g2:=ajouttel (nunsterm !t i) !g2;si:=(0,z,ajouttel gg2 (cl !t i))::(!si);end
						else si:=(0,z,(cl !t i))::(!si);
					end
					else begin
						t:= [R(0,0)];
						if a && che pik (x+1) <> che pij (x+1) then t:=!g1
						else if b && che pij (y+1) <> che pik (y+1) then t:=!g2;
						si:=(0,-z,!t)::(!si);
					end;
				end;
			done;
			((!g1,!g2),!si) end;;

let rec trouvesplit p1 p2 n l= (*cherche le split de 2 pi*)
	match p1 with
		[] -> (n,p1,p2,l)
		|p::q -> begin match p2 with
			[] -> (n,p1,p2,l)
			|r::s -> if r=p then trouvesplit q s (n+1) (l@[p])
													else (n,p1,p2,l);end;;

let rec cherchepij lp l j i= (* Find i and j such that split (l, pij) is not already in si*)
	match lp with
		[] -> (false,0)
		|p::q -> let (a,b,c,d)=trouvesplit l p 0 [] in if a=0 || i <> fst3(List.hd(d)) then (true,j) else cherchepij q l (j+1) i;;

let rec chercheij lpi i= (* Find i and j such that split (pii, pij) is not already in si *)
	match lpi with
		[] -> failwith ("Did you write a protocol? i think it's empty ")
		|[a]-> failwith ("No valid split...")
		|p::r-> let (x,y) = cherchepij r p 1 i in
						if x then (i,(i+y)) else chercheij r (i+1);;

let rec contrib i pj l=
match pj with
[] -> l
|[(a,_,b)] -> failwith("An even number of elements? ? (attack4)")
|(c,_,s)::x::q when c=i -> contrib i q (ajouttel s l)
|_::_::q -> contrib i q l;;

let rec upd pij=
	match pij with
		[] -> []
		|[(a,_,b)] -> failwith("An even number of elements? ? (attack4)")
		|[(a,b,c);(d,e,f)] -> (a,b,ajouttel f c)::[(d,e,f)]
		|[x;y;z] -> failwith("An even number of elements? ? (attack4)")
		|(a,b,z)::(c,d,e)::(f,g,h)::q-> (a,b,ajouttel e z)::(c,d,e)::upd ((f,g,enlevel e h)::q);;

let rec updl l=
	match l with
		[] -> []
		|p::q -> (upd p)::(updl q);;

let tablcij pij n= (* Let's build the contribution table... if need be *)
	let l=ref pij and t=Array.make_matrix n n [] in begin
		for j=1 to n do
			let l1=List.hd(!l)in
			for i=1 to n do
				t.(i-1).(j-1)<-contrib i l1 [U];
			done;
			if j<n then l:=List.tl(!l);
		done;
		t;
	end;;

let rec cherchist t i lt l= (*Is t here? let's add it if not*)
	match lt with
	[] -> l@[(t,i)]
		|[]::q -> cherchist t i q l
		|((a,b)::q)::r -> if a = t then l@[(t,b)] else cherchist t i (q::r) l;;

let rec traithist p i lt l=
	match p with
		[] -> lt@[l]
		|t::q -> traithist q i lt (cherchist t i lt l);;

let rec hist i lpi lt=
	match lpi with
		[] -> lt
		|p::q -> hist (i+1) q (traithist p i lt []);;

let rec qcle l=
	match l with
		[] -> []
		|(a,b,_)::q -> (a,b)::(qcle q);;

let rec qclean l=
	match l with
		[] -> []
		|p::q -> qcle(p)::qclean q;;

let tablhist l= (* Let's start the story array *)
	let l1=ref (hist 1 (qclean l) []) in
		let t=Array.make (List.length !l1) [] in begin
			for i = 0 to (List.length !l1 -1) do
				t.(i)<-(List.hd (!l1));
				l1:=List.tl(!l1);
			done;
		t;end;;

let rec replaceb l j i= (* Replace value send by the victim, by the ones from the adversary *)
	match l with
		[] -> []
		|p::q -> match p with
			M1(y) -> M1(replaceb y j i)::(replaceb q j i)
			|R(a,b) -> if a=j then R(i,b)::(replaceb q j i) else p::(replaceb q j i)
			|K(a,b) -> if a=j then K(i,b)::(replaceb q j i) else if b=j then K(a,i)::(replaceb q j i)else p::(replaceb q j i)
			|_ -> p::(replaceb q j i);;

let rec replace2 li j i=
	match li with
		[] -> []
		|(a,b,p)::q -> if a<>j then (a,b,(replaceb p j i))::(replace2 q j i) else (0,b,(replaceb p j i))::(replace2 q j i) ;;

let rec replace2b lpi j i=
	match lpi with
		[] -> []
		|p::q -> (replace2 p j i)::(replace2b q j i);;

let rec replacel l lj i=
	match lj with
		[] -> l
		|p::q -> replacel (replace2b l p i) q i;;

let rec enlevek i l=(* Remove the long term key, i = 0 is the adversary, i > 0 is the user i *)
	match l with
	[] -> []
	|p::q ->  match p with
				M1(y) -> M1(enlevek i y)::(enlevek i q)
				|K(a,b) -> if a=i || b=i then (enlevek i q) else p::(enlevek i q)
				|R(a,b) -> if a=i then (enlevek i q) else p::(enlevek i q)
				|_ -> p::(enlevek i q);;

let rec message2 c= (*contrib2stringlatex*)
	match c with
	[] -> ""
	|p::q -> begin match p with
						M1(l) ->"{"^(message2 l)^"}^{-1}"^message2 q
						|R(a,b) ->"R_{"^string_of_int(a)^","^string_of_int(b)^"}"^message2 q
						|K(a,b) ->"K_{"^string_of_int(a)^string_of_int(b)^"}"^message2 q
						|_ -> "";end;;

let rec printlc2 l p=
	match l with
		[] -> ()
		|(a,b,c)::q -> let n=if List.length q=0 then "" else "\\ar@{=>}[d] " in
		let s=if b < 0 then "{\\bullet}"^n^" \\ar[r]^{"^(message2 c)^"}& {\\bullet}"^n^" \\\\ \n"
		else "{\\bullet}"^n^" & {\\bullet}"^n^" \\ar[l]_{"^(message2 c)^"} \\\\ \n" in begin output_string p s; printlc2 q p; end;;



let rec miroir l ll=
	match l with
	[] -> ll
	|p::q -> miroir q (p::ll);;

let printlc l p i j gs=
	output_string p ("\\begin{figure}[!h]\n");
	output_string p ("\\centering\n");
	output_string p ("\\[\\xymatrix@C=4cm@R=.8cm { {s_0} & {s_{"^string_of_int(i)^"}} \\\\ \n");
	printlc2 (miroir l []) p;
	output_string p ("}  \\]\n");
	output_string p ("\\caption{The adversary speaks with $"^string_of_int i ^"$ pretending to be $"^string_of_int j ^"$}\n");
	output_string p ("\\end{figure}\n");
	output_string p ("\n");;

let fstf x = fst(fst x);;
let sndf x = snd(fst x);;

let clk (a,b) =
(enlevek 0 a, enlevek 0 b);;

let calculp2 i j k sjj skk t lpi filename= (* Product of the contributions, like the attacker *)
	let g=ref (([U],[U]),[]) and gs=ref ([U],[U]) and sk = ref skk and sj=ref sjj and p=open_out (filename^".tex") in
		let sjsa=replacel lpi sjj 0 and sksa=replacel lpi skk 0 in begin
			output_string p ("\\documentclass{article}\n");
			output_string p ("\\usepackage[latin1]{inputenc}\n");
			output_string p ("\\usepackage[T1]{fontenc}\n");
			output_string p ("\\usepackage{geometry}\n");
			output_string p ("\\usepackage[francais]{babel}\n");
			output_string p ("\\usepackage[all]{xy}\n");
			output_string p ("\\def\\labelstyle{\\textstyle}\n");
			output_string p ("\\begin{document}\n");
			output_string p ("\\centering \n");
			g:=(algo1 i i j ([U],[U]) t lpi);
			if fst !g <> !gs then printlc (snd !g) p i j !gs else
				output_string p ("$C^{-1}(M_"^string_of_int i ^"~\\rightarrow~M_"^string_of_int i ^").C(M_"^string_of_int i ^"~\\rightarrow~M_"^string_of_int j ^") = 1$ \n");
			gs:= clk(fst !g);
			g:=(algo1 i j k (fst !g) t lpi);
			if fst !g <> !gs then printlc (snd !g) p i k !gs else
				output_string p ("$C^{-1}(M_"^string_of_int i ^"~\\rightarrow~M_"^string_of_int j ^").C(M_"^string_of_int i ^"~\\rightarrow~M_"^string_of_int k ^")$ = 1 \n");
			gs:= clk(fst !g);
			while !sk <> [] do
				let ii=List.hd !sk in begin
					g:=(algo1 ii i k (fst!g) t sjsa);
					if fst !g <> !gs then printlc (snd !g) p ii k !gs else
				output_string p ("$C^{-1}(M_"^string_of_int ii ^"~\\rightarrow~M_"^string_of_int i ^").C(M_"^string_of_int ii ^"~\\rightarrow~M_"^string_of_int k ^")$ = 1 \n");
					gs:= clk(fst !g);
					sk:=List.tl(!sk);
			end;done;
			while !sj <> [] do
				let ii=List.hd !sj in begin
					g:=(algo1 ii i j (fst !g) t sksa);
					if fst !g <> !gs then printlc (snd !g) p ii j !gs else
				output_string p ("$C^{-1}(M_"^string_of_int ii ^"~\\rightarrow~M_"^string_of_int i ^").C(M_"^string_of_int ii ^"~\\rightarrow~M_"^string_of_int k ^")$ = 1 \n");
				gs:= clk(fst !g);
					sj:=List.tl(!sj);
			end;done;
			output_string p ("\\newpage \n");
			output_string p (" The previous exchanges allows to get the session key $"^ message2 (enlevek 0 (sndf !g)) ^"$ \n");
			output_string p ("\\end{document}\n");
			close_out p;
			(enlevek 0 (fstf !g),enlevek 0 (sndf !g));
		end;;



let rec cpmodift l lt ltt=
	match l with
		[] -> ltt
		|[]::s -> cpmodift s [] ltt@[lt]
		|[(a,b,c)]::s -> failwith(" An even number of elements, that's odd... (attack 3) ")
		|[(a,b,c);(d,e,f)]::s -> cpmodift s [] ltt@[lt@[(a,b,ajouttel f c);(d,e,f)]]
		|((a,b,c)::((d,e,f)::((g,h,i)::q)))::s ->cpmodift (((g,h,enlevel f i)::q)::s) (lt@[(a,b,ajouttel f c);(d,e,f)]) ltt;;

let calculp i j k sjj skk t lpi filename= (* Now we multiply every contributions *)
	calculp2 i j k sjj skk t lpi filename;;


let rec toutsf n a b= (* [|1;n|]\{a}\{b} *)
	if n=0 then []
		else if (n<>a)&&(n<>b) then n::(toutsf (n-1) a b) else (toutsf (n-1) a b);;

let rec start i lpi= (* Let the fun begins *)
	if i=1 then fst3(List.hd(List.hd(lpi)))
		else start (i-1) (List.tl (lpi));;

let start3 lpi i j k=
	(start i lpi, start j lpi, start k lpi);;

let rec appartient a l=
	match l with
		[] -> false
		|p::q -> if p=a then true else appartient a q;;

let nbs i j k sj sk t lpi= (*Testing the 4 propositions*)
	let spl=ref 0 and sp=ref 0 and sm=ref 0 and(a,b,c)=start3 lpi i j k and r4a=ref (0,0) and r4b=ref(0,0) and act=ref false in
		let qk = (a=c) and qj= (a=b) and qi = (b=c) in begin
			if not(qj) then begin
				if a=i then begin incr sm;r4a:=(i,j);act:=true;end;
				if b=i then begin incr sp;r4a:=(i,j);act:=true;end;end;
			if not(qi) then begin
				if b=i then begin incr sm;if not(!act) then begin r4a:=(j,k);act:=true;end else r4b:=(j,k); end;
				if c=i then begin incr sp;if not(!act) then begin r4a:=(j,k);act:=true;end else r4b:=(j,k); end;
				end else if (i=b) then incr spl;
			if not qk then begin
				if appartient a sk then begin incr sm;if not(!act) then begin r4a:=(i,k);act:=true;end else r4b:=(i,k); end;
				if appartient c sk then begin incr sp;if not(!act) then begin r4a:=(i,k);act:=true;end else r4b:=(i,k); end;
				end else if appartient a sk then incr spl;
			if not qj then begin
				if appartient a sj then begin incr sm;if not(!act) then begin r4a:=(i,j);act:=true;end else r4b:=(i,j); end;
				if appartient b sj then begin incr sp;if not(!act) then begin r4a:=(i,j);act:=true;end else r4b:=(i,j); end;
				end else if appartient a sj then incr spl;
			(!spl,!sm,!sp,!r4a,!r4b);end;;

let nbs2 i j k sj sk t lpi= (*Comme nbs, mais plus d'info pour l'ordre sur les contributions, s'utilise dans lecas � 4 et � 3*)
	let spl=ref 0 and sp=ref 0 and sm=ref 0 and(a,b,c)=start3 lpi i j k and r4a=ref (0,0,0) and r4b=ref(0,0,0) and act=ref false in
		let qk = (a=c) and qj= (a=b) and qi = (b=c) in begin
			if not(qj) then begin
				if a=i then begin incr sm;r4a:=(i,j,i);act:=true;end;
				if b=i then begin incr sp;r4a:=(i,j,i);act:=true;end;end;
			if not(qi) then begin
				if b=i then begin incr sm;if not(!act) then begin r4a:=(j,k,i);act:=true;end else r4b:=(j,k,i); end;
				if c=i then begin incr sp;if not(!act) then begin r4a:=(j,k,i);act:=true;end else r4b:=(j,k,i); end;
				end else if (i=b) then incr spl;
			if not qk then begin
				if appartient a sk then begin incr sm;if not(!act) then begin r4a:=(i,k,a);act:=true;end else r4b:=(i,k,a); end;
				if appartient c sk then begin incr sp;if not(!act) then begin r4a:=(i,k,c);act:=true;end else r4b:=(i,k,c); end;
				end else if appartient a sk then incr spl;
			if not qj then begin
				if appartient a sj then begin incr sm;if not(!act) then begin r4a:=(i,j,a);act:=true;end else r4b:=(i,j,a); end;
				if appartient b sj then begin incr sp;if not(!act) then begin r4a:=(i,j,b);act:=true;end else r4b:=(i,j,b); end;
			end else if appartient a sj then incr spl;
(!spl,!sm,!sp,!r4a,!r4b);end;;

let test i j k sj sk t lpi=
	let (spl,sm,sp,r4a,r4b)=nbs i j k sj sk t lpi in
		(spl<=1 && sp+sm=0)||(spl=0&&((sp+sm=1)||(sp*sm=1 && (r4a=r4b))));;

let rec ff a l=
	match l with
		[] -> failwith("The key is supposed to be generated from everyone, here someone is not speaking");
		|(c,b,_)::q -> if c=a then b else ff a q;;

let rec prem (a,b,c) l=(* Who comes first on sc pa or pb ? *)
	ff c (pj a l) < ff c (pj b l);;

let prems a b l=(* Are we in the special condition? *)
	prem a l || prem b l;;

let test4 i j k sj sk t lpi=
	let (spl,sm,sp,r4a,r4b)=nbs2 i j k sj sk t lpi in
	(spl<=1 && sp+sm=0)||(spl=0&&((sp+sm=1)||(sp*sm=1 && (r4a=r4b))))||(sp*sm=1 && prems r4a r4b lpi);;
(* If we are running attack4, only the last test can be true. In case of attack 3, the other might allows to handle some extra cases for free *)

let attack5 t lpi filename=
	let i=ref 1 and j=ref 2 and k=ref 3 and n=List.length lpi in begin
		while not((test !i !j !k [!k] (toutsf n !k !i) t lpi)||(test !i !j !k  (toutsf n !j !i) [!j] t lpi))do
			incr k;
			if !k = 6 then incr j;
			if !j = 5 then begin incr i;j:=1;end;
			if !k = 6 then k:=1;
			if !j= !i then incr j;
			if !k= !i then incr k;
			if !k= !j then incr k;done;
		if (test !i !j !k [!k] (toutsf n !k !i) t lpi)
			then calculp !i !j !k [!k] (toutsf n !k !i) t lpi filename
			else calculp !i !j !k (toutsf n !j !i) [!j] t lpi filename;end;;

let rec elim l =
	match l with
  	[] -> []
  	|(a,b,c,d)::q -> if a=1||b=2||c=3||d=4||a=b||a=c||a=d||b=c||b=d||c=d then elim q else (a,b,c,d)::(elim q);;

let creel ()=
	let l=ref [] in begin
		for i=2 to 4 do for j=1 to 4 do for k=1 to 4 do for ll=1 to 3 do
			l:=(i,j,k,ll)::(!l);done;done;done;done;!l;
		end;;

let attack4 t lpi filename=
let i=ref 1 and j=ref 2 and k=ref 3 and n=4 in
let sj=ref [!k] and sk=ref (toutsf n !k !i) and a=start 1 lpi and b=start 2 lpi and c=start 3 lpi and d=start 4 lpi in begin
if appartient (a,b,c,d) (elim (creel ())) then (* if one of the 9 special cases*)
if a=2 then (* To be faster, we directly feed the solution in those cases *)
		 if b=1 then if test4 1 3 2 [2] [3;4] t lpi then begin i:=1;j:=3;k:=2;sj:=[2];sk:=[3;4]; end else begin i:=3;j:=1;k:=4;sj:=[4];sk:=[1;2]; end
		 else if b=3 then if test4 3 1 2 [2] [1;4] t lpi then begin i:=3;j:=1;k:=2;sj:=[2];sk:=[1;4]; end else begin i:=1;j:=3;k:=4;sj:=[4];sk:=[2;3]; end
		 else if test4 2 3 4 [4] [1;3] t lpi then begin i:=2;j:=3;k:=4;sj:=[4];sk:=[1;2]; end else begin i:=3;j:=2;k:=1;sj:=[1];sk:=[2;4]; end
else if a=3 then
		 if b=1 then if test4 3 2 4 [4] [1;2] t lpi then begin i:=3;j:=2;k:=4;sj:=[4];sk:=[1;2]; end else begin i:=2;j:=3;k:=1;sj:=[1];sk:=[3;4]; end
		 else if b=2 then if test4 1 2 3 [3] [2;4] t lpi then begin i:=1;j:=2;k:=3;sj:=[3];sk:=[2;4]; end else begin i:=2;j:=1;k:=4;sj:=[4];sk:=[1;3]; end
		 else if test4 1 2 4 [4] [2;4] t lpi then begin i:=1;j:=2;k:=4;sj:=[4];sk:=[2;3]; end else begin i:=2;j:=1;k:=3;sj:=[3];sk:=[1;4]; end
else if b=1 then if test4 2 4 3 [3] [1;4] t lpi then begin i:=2;j:=4;k:=3;sj:=[3];sk:=[1;4]; end else begin i:=4;j:=2;k:=1;sj:=[1];sk:=[2;3]; end
		 else if b=2 then if test4 2 1 4 [4] [1;3] t lpi then begin i:=2;j:=1;k:=4;sj:=[4];sk:=[1;3]; end else begin i:=1;j:=2;k:=3;sj:=[3];sk:=[2;4]; end
		 else if test4 1 2 4 [4] [2;3] t lpi then begin i:=1;j:=2;k:=4;sj:=[4];sk:=[2;3]; end else begin i:=2;j:=1;k:=3;sj:=[3];sk:=[1;4]; end
else begin (* otherwise the generic method will work *)
	while not((test !i !j !k [!k] (toutsf n !k !i) t lpi)||(test !i !j !k  (toutsf n !j !i) [!j] t lpi))do
		incr k;
		if !k = 5 then incr j;
		if !j = 5 then begin incr i;j:=1;end;
		if !j= !i then incr j;
		if !k = 5 then k:=1;
		if !k= !i then incr k;
		if !k= !j then incr k;
		sj:=[!k]; sk:= (toutsf n !k !i);
	done;
	if (test !i !j !k  (toutsf n !j !i) [!j] t lpi) then begin
	sj:=(toutsf n !j !i);
	sk:=[ !k];end;
end;
calculp !i !j !k !sj !sk t lpi filename;end;;

let attack3 t lpi filename=
	let i=ref 1 and j=ref 2 and k=ref 3 and a=start 1 lpi and b=start 2 lpi and c=start 3 lpi in
		if a=1 && c=3 && b=2 then if prem (3,2,1) lpi then calculp 3 1 2 [2] [1] t lpi filename else calculp 2 1 3 [3] [1] t lpi filename 
		else if a=2 && c=1 && b=3 then if prem (2,1,3) lpi then calculp 2 3 1 [1] [3] t lpi filename else calculp 1 3 2 [2] [3] t lpi filename 
		else if a=3 && c=2 && b=1 then if prem (1,3,2) lpi then calculp 1 2 3 [3] [2] t lpi filename else calculp 3 2 1 [1] [2] t lpi filename 
		else begin
			while not((test4 !i !j !k [!k] [!j] t lpi)||(test4 !i !k !j [!j] [!k] t lpi)) do
				incr k;
				if !k = 4 then incr j;
				if !j = 4 then begin incr i;j:=1;end;
				if !j= !i then incr j;
				if !k = 4 then k:=1;
				if !k= !i then incr k;
				if !k= !j then incr k;
				if !i > List.length lpi then failwith("Many cases with 3 users don't have a generic attack");
			done;
			if (test4 !i !j !k [!k] [!j] t lpi) then calculp !i !j !k  [!k] [!j] t lpi filename else calculp !i !k !j [!j] [!k] t lpi filename;
		end;;
