let ecritp=open_out (Sys.argv.(1)^".tex");;

let hyp=ref 0;;

let compth () =
	incr hyp;
	string_of_int(!hyp);;

let rec message2 c=(*contrib2stringlatex*)
	match c with
		[] -> ""
		|p::q -> begin match p with
			M1(l) ->"{("^(message2 l)^")}^{-1}"^message2 q
			|R(a,b) ->"R_{"^string_of_int(a)^","^string_of_int(b)^"}"^message2 q
			|K(a,b) ->"K_{"^string_of_int(a)^string_of_int(b)^"}"^message2 q
			|_ -> "";end;;

let rec tupd pij=
	match pij with
		[] -> []
		|[(a,_,b)] -> failwith("Even number of elements (attack 4?)")
		|[(a,b,c);(d,e,f)] -> (a,b,ajouttel f c)::[(d,e,f)]
		|[x;y;z] -> failwith("Even number of elements (attack 4?)")
		|(a,b,z)::(c,d,e)::(f,g,h)::q-> (a,b,ajouttel e z)::(c,d,e)::tupd ((f,g,enlevel e h)::q);;
	
let rec tupdl l=
	match l with
		[] -> []
		|p::q -> (tupd p)::(tupdl q);;

let test a =
	if a=M1([]) then [] else [a];;

let rec tcl p=
	match p with
		[] -> []
		|p::q -> match p with
			M1(y) -> test(M1(tcl y))@(tcl q)
			|R(a,b) -> if a=0 then tcl q else p::(tcl q)
			|K(a,b) -> if a=0 || b=0 then tcl q else p::(tcl q)
			|_ -> p::(tcl q);;

let actuel=ref 0;;

let pop i= if i then !actuel else begin incr actuel; !actuel; end;;
				
let rec linclt y z=
	match z with
		[] -> false
		|p::q -> if p=y then true else linclt y q;;

let rec tdans p l=
	match p with
		M1(y) -> begin match l with
			[] -> false
			|t::q -> match t with M1(z) -> linclt (List.hd(y)) z || tdans p q 
			|_ -> tdans p q;
			end
		|_ -> begin match l with
			[] -> false
			|t::q -> if p=t then true else tdans p q;
			end;;

let text (a,b)= "$s_"^string_of_int a ^"("^string_of_int b^")$";;															

let rec checkl l=
	match l with
		[] -> []
		|p::q -> if List.length (enleve p q)<List.length q then checkl (enleve p q) else p::(checkl q);;
					
let rec moinsliste l= (* If switching g1 g2 we swap constraints*)
	match l with
		[] -> []
		|p::q ->  match p with
			M1(y) -> ajouttel y (moinsliste q)
			|_ -> enleve p (moinsliste q);;

let choix (a,b) c= if c then a else b;;

let ordre l (a,b) bo=(* if bo then l = lpi*)
	if bo then (l,b) else (a,l);;

let rec sit a ll=
	match ll with
		[] -> false
		|p::q -> a=fst(List.hd(p)) || sit a q;;

let rec etete l=
	match l with
		[] -> []
		|p::q -> List.tl(List.tl(p)):: etete q;;

let rec tcherche p lpi lc lt ltt ii lplh bo lpisa= (*ltt@(lt@(p::q)::s*)
	if ii >20 then begin output_string ecritp ("-- PMax depth reached, let's abort and feel sad \n \\\\");(false,true); end else begin
	match lpi with
		[] -> begin output_string ecritp ("-- Cannot cancel $"^message2 [p]^"$ -- \n \\\\");(false,false); end
		|[]::s -> tcherche p s lc [] (ltt@[lt]) ii lplh bo lpisa
		|[(a,b)]::s -> failwith("Even number of elements ... (attack3)")
		|(((a,b,c),i)::((d,e,f),j)::q)::s -> if (i=0||i=pop true) && List.length b > (List.length(enleve p b)) then
		let ctr=checkl((ajouttel (enleve p b) lc)) and ss=compth () and lll = ref (ltt@((lt@((a,b,c),pop (i= pop true))::((d,e,f),j)::q))::s)
		and g=choix ("$g_1$","$g_2$") bo in begin 
		output_string ecritp ("Start "^ss ^": We try to cancel $"^message2 [p]^"$ using previous computation "^text (a,c)^"\n \\\\");
		if ctr <> [] then begin output_string ecritp ("We still need to cancel: $"^message2 ctr^"$ \n \\\\");
		if sit (a,b,c) lpisa then begin 
			output_string ecritp ("From here on "^g^" can not use new starting points \n \\\\");
			lll := etete (!lll);
		end;
		let (aa,bb)=tok (ordre !lll lplh bo) ctr (ii+1) bo lpisa in
		if aa then begin
			output_string ecritp ("End "^ss ^" : We did it \n \\\\");
			(true,bb);
		end 
		else begin
		output_string ecritp ("End "^ss ^" : Oh noes :() \n \\\\");
		tcherche p (q::s) lc (lt@[((a,b,c),i);((d,e,f),j)]) ltt ii lplh bo lpisa;end;end else (true,false);end
		else tcherche p (q::s) lc (lt@[((a,b,c),i);((d,e,f),j)]) ltt ii lplh bo lpisa;end
		and tok (lpi,lpih) lcontrainte i b lpisa=(* if f we can do starting points, otherwise no *)
		match tcl lcontrainte with
			[] -> begin output_string ecritp (">>> No more constraints, we did it <<< \\\\\n"); (true,false); end
		|p::q -> match p with
			M1(y) -> begin let (aa,bb)=tcherche (M1([List.hd y])) (choix (lpi,lpih) b) (checkl(tcl (enleve (List.hd y) lcontrainte))) [] [] (i+1) (lpi,lpih) b lpisa in
			if aa then (true,bb) else let (cc,dd)=tcherche (List.hd y) (choix (lpih,lpi) b) (checkl(tcl (moinsliste (enleve (List.hd y) lcontrainte)))) [] [] (i+1) (lpi,lpih) (not b) lpisa in
			(cc,bb||dd);end  (* choice are inverted to avoid using not b *)
			|_ -> tcherche p (choix (lpi,lpih) b) (tcl q) [] [] (i+1) (lpi,lpih) b lpisa;;

let rec headless lpi=
	match lpi with
		[] -> []
		|p::q -> (List.tl(List.tl(p))::(headless q));;			
				
let rec modift l lt ltt=
	match l with
		[] -> ltt
		|[]::s -> modift s [] ltt@[lt]
		|[(a,b,c)]::s -> failwith("Even number of elements... (attack3)")
		|[(a,b,c);(d,e,f)]::s -> modift s [] ltt@[lt@[(a,ajouttel f c,b),0;(d,f,e),0]]
		|((a,b,c)::((d,e,f)::((g,h,i)::q)))::s ->modift (((g,h,enlevel f i)::q)::s) (lt@[(a,ajouttel f c,b),0;(d,f,e),0]) ltt;;

let rec ttrfin l=
	match l with
		[] -> failwith("oups")
		|[b,c,a] ->enlevel a [R(1,1);R(2,1);R(3,1)]
		|p::q -> ttrfin q;;

let rec transfofin i lpi=
	if i =1 then ttrfin(List.hd lpi) else transfofin (i-1) (List.tl lpi);;

let ttesti lpi i =
	let lpii= modift lpi [] [] and lf = transfofin i lpi in	tok (lpii,headless lpii) lf 0 true lpii;;

let rec ieme l i=
	match l with
		[] -> failwith("Random too big")
		|p::q -> if i=1 then p else ieme q (i-1);;

let rec deel l i j=
	match l with
		[] -> []
		|p::q -> if p=i ||p=j then deel q i j else p::(deel q i j);;

let test3 lpi=
	let res=ref(false,false) in begin
		Random.self_init  ();
		output_string ecritp ("\\documentclass{article}\n");
		output_string ecritp ("\\usepackage[latin1]{inputenc}\n");
		output_string ecritp ("\\usepackage[T1]{fontenc}\n");
		output_string ecritp ("\\usepackage{geometry}\n");
		output_string ecritp ("\\usepackage[all]{xy}\n");
		output_string ecritp ("\\def\\labelstyle{\\textstyle}\n");
		output_string ecritp ("\\begin{document}\n ~ \n \\\\");
		let l=[1;2;3] and i=(Random.int 3)+1 and j=ref ((Random.int 2)+1) and k=ref 0 in begin
			j:=ieme (deel l i i) !j;
			k:=List.hd (deel l i !j);
			res:=ttesti lpi i;
			if not(fst !res) then begin
				output_string ecritp (" User "^string_of_int i^" cannot be attacked, we now focus on "^string_of_int !j^" \\newpage  ~ \\\\ \n");
				let (aa,bb)= ttesti lpi !j in res:=(aa,snd(!res)||bb);
				if not(fst !res) then begin output_string ecritp (" User "^string_of_int !j^" cannot be attacked, we now focus on "^string_of_int !k^" \\newpage ~ \\\\ \n");
					let (aa,bb)= ttesti lpi !k in res:=(aa,snd(!res)||bb); 
					if fst !res then output_string ecritp (" User "^string_of_int !k^" can be attacked \n") 
						else output_string ecritp (" User  "^string_of_int !k^" cannot be attacked  \n");
				end
				else output_string ecritp (" User "^string_of_int !j^" can be attacked \n"); end else
					output_string ecritp (" User "^string_of_int i^" can be attacked \n"); 
			output_string ecritp ("\\end{document}\n");
			close_out ecritp; !res; 
		end;
	end;;