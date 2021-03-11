package rs.ac.bg.etf.pp1;

import java.util.ArrayList;
import java.util.Stack;

import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.mj.runtime.Code;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.Obj;
import rs.etf.pp1.symboltable.concepts.Struct;

public class CodeGenerator extends VisitorAdaptor {

	private static final int arrayRef = 33;

	private int varCounter = 0;

	private int paramCounter = 0;

	private int mainPc;

	// za inicijalizatorske liste
	private int currElem; // naredni element za upis u inicijalizatorsku listu

	public int getMainPc() {
		return mainPc;
	}

	// ******************* obrada ************************************
	// tekuca operacija koja se obradjuje (add, sub...)
	Stack<Character> operations =  new Stack<>();
	// za relacije
	String relOp;

	// ja probam ******
	Struct methodType = Tab.noType;

	public void visit(Program program) {
		int i = 0;
		for (Obj o : program.getProg_name().obj.getLocalSymbols()) {
			if (o.getKind() == Obj.Var)
				i++;
		}
		Code.dataSize = i;
		Tab.closeScope(); // ovde je kraj kraj pa moze close scope
	}

	public void visit(RetType t) {
		t.obj.setAdr(Code.pc);
		methodType = t.getType().struct;
		// zbog globalnih promenljivih, da se one ne bi racunale
		varCounter = paramCounter = 0;

	}

	public void visit(VoidRetType t) {
		if ("main".equalsIgnoreCase(t.getId()))
			mainPc = Code.pc;
		t.obj.setAdr(Code.pc);
		// zbog globalnih promenljivih, da se one ne bi racunale
		varCounter = paramCounter = 0;

	}

	public void visit(Var VarDecl) {
		varCounter++;
	}

	public void visit(VarArray VarDecl) {
		varCounter++;
	}

	public void visit(ScalarPar FormalParam) {
		paramCounter++;
	}

	public void visit(ArrayPar FormalParam) {
		paramCounter++;
	}

	public void visit(CloseScopeClass c) {
		// ovde smo prosli promenljive i sad generisemo enter
		Code.put(Code.enter);
		Code.put(paramCounter);
		Code.put(paramCounter + varCounter);
		paramCounter = varCounter = 0;
	}

	public void visit(MethodDec methodDecl) {
		Code.put(Code.exit);
		Code.put(Code.return_);

		// generisanje koda
		if (methodType == Tab.noType) { // ***** zar ne bi onda trebalo u ret expr staviti methodType = Tab.noType ?
										// ****
			Code.put(Code.exit);
			Code.put(Code.return_);
		} else { // end of function reached without a return statement
			Code.put(Code.trap);
			Code.put(1);
		}
	}

	public void visit(ReturnExprStmt ReturnExpr) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}

	public void visit(ReturnStmt ReturnNoExpr) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}

	// ------------------ designator --------------------------

	public void visit(SimpleDesignator designator) {
		// ako je rec o pozivu neke od ugradjenih funkcija ne stavljamo nista na stek
		String name = designator.obj.getName();
		if (name.equals("len") || name.equals("chr") || name.equals("ord")) {
			return;
		}
		SyntaxNode parent = designator.getParent().getParent(); // parrent od designator je Designator, uvek. nama treba
																// ono iznad Designator
		if (DesAsign.class != parent.getClass() && FuncCall.class != parent.getClass()
				&& FuncCallNoPar.class != parent.getClass() && DesFuncCall.class != parent.getClass()
				&& DesProcCall.class != parent.getClass() && ReadStmt.class != parent.getClass()) {
			Code.load(designator.obj);
		}
		// ako je niz i radimo new ili dodelu jednog niza drugom radicemo store, ne
		// astore
		if (designator.obj.getType().getKind() == Struct.Array) {
			designator.obj.setFpPos(arrayRef);
		}

	}

	public void visit(ArrayIdent ident) {
		// na stek stavimo objekat koji je adr za pristup elementu niza
		Code.load(ident.obj);
	}

	public void visit(ArrayDesignator designator) {
		// na steku su vec adr i indeks
		// stavimo samo odgovarajucu instrukciju
		// ako nije u pitanju dodela radimo load
		// *** i ako nije u pitanju instrukcija read! ***
		SyntaxNode parent = designator.getParent().getParent();
		// ako je u pitanju desInc ili desDec ono sto smo loadovali je za store, sad nam
		// treba isto to za load
		if (parent.getClass() == DesInc.class || parent.getClass() == DesDec.class) {
			Code.put(Code.dup2); // duplira adresu i expr na vrhu steka
		}

		if (parent.getClass() != DesAsign.class && parent.getClass() != ReadStmt.class) {
			int arrayKind = designator.obj.getType().getElemType().getKind();
			if (arrayKind == Struct.Int)
				Code.put(Code.aload);
			else
				Code.put(Code.baload);
		}

	}

	public void visit(EnumDesignator designator) {
		// na stek treba da stavimo vrednost, tj objekat konstante koja se koristi
		Obj wholeEnum = Tab.find(designator.getId());
		for (Obj obj : wholeEnum.getLocalSymbols()) {
			if (obj.getName().equals(designator.getId2())) {
				// nasli smo nas enum
				Code.load(obj);
				break;
			}
		}
	}

	// ---------------------------------------------------------

	public void visit(DesAsign assignment) {
		// ako je u pitanju element niza radimo astore ili bastore,
		// a ako je simple designator radimo store
		// ali ako dodeljujemo nizu vrednost onda je samo store (kod new npr)
		// *********************************** !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
		// *******************
		Obj obj = assignment.getDesignator().obj;
		if (obj.getType().getKind() == Struct.Array && obj.getFpPos() != arrayRef) {
			if (obj.getType().getElemType().getKind() == Struct.Int)
				Code.put(Code.astore);
			else
				Code.put(Code.bastore);
		} else {
			Code.store(obj);
			obj.setFpPos(0); // vise nam ne treba
		}
		// ovde mozemo da ubacimo vrednosti elemenata ako je bilo inicijalizatorske
		// liste

	}

	public void visit(DesInc des) {
		// na steku je vec designator
		Obj obj = des.getDesignator().obj;
		Code.loadConst(1);
		Code.put(Code.add);
		if (obj.getType().getKind() == Struct.Array) {
			if (obj.getType().getElemType().getKind() == Struct.Int)
				Code.put(Code.astore);
			else
				Code.put(Code.bastore);
		} else {
			Code.store(obj);
		}

	}

	public void visit(DesDec des) {
		// na steku je vec designator
		Obj obj = des.getDesignator().obj;
		Code.loadConst(-1);
		Code.put(Code.add);
		if (obj.getType().getKind() == Struct.Array) {
			if (obj.getType().getElemType().getKind() == Struct.Int)
				Code.put(Code.astore);
			else
				Code.put(Code.bastore);
		} else {
			Code.store(obj);
		}

	}
	// ------------- u izrazu --------------------------

	public void visit(FuncCallNoPar funcCall) {
		Obj o = funcCall.getDesignator().obj;
		int dest_adr = o.getAdr() - Code.pc; // racunanje relativne adrese
		Code.put(Code.call);
		Code.put2(dest_adr);
	}

	public void visit(FuncCall funcCall) {
		// ukoliko je neka od predefinisanih metoda prosto ovde uradimo sta se trazi
		if (funcCall.getDesignator().obj.getName().equals("len")) {
			// adresa niza je na steku
			Code.put(Code.arraylength);
			// sad je rezultat na steku
			return;
		} else if (funcCall.getDesignator().obj.getName().equals("chr")) {
			// chr - konverzija int to char; int je na steku
			return;
		} else if (funcCall.getDesignator().obj.getName().equals("ord")) {
			// char to int; char je na steku
			return;

		}
		Obj o = funcCall.getDesignator().obj;
		int dest_adr = o.getAdr() - Code.pc; // racunanje relativne adrese
		Code.put(Code.call);
		Code.put2(dest_adr);
	}

	// -------------------------------------------------

	public void visit(IntRef intRef) {
		// napravimo objekat samo za potrebe smestanja na stek
		Obj o = new Obj(Obj.Con, "", Tab.intType);
		o.setAdr(intRef.getI());
		Code.load(o);
	}

	public void visit(CharRef charRef) {
		Obj o = new Obj(Obj.Con, "", Tab.charType);
		o.setAdr(charRef.getC());
		Code.load(o);
	}

	public void visit(BoolRef boolRef) {
		Obj o = new Obj(Obj.Con, "", Compiler.boolStruct);
		o.setAdr(boolRef.getB() ? 1 : 0);
		Code.load(o);
	}

	public void visit(OperatorNew operatorNew) {
		// sa steka kupi velicinu
		// *** 0 ili 1 bi trebalo da budu argumenti funkcije! ***
		Code.put(Code.newarray);
		if (operatorNew.getType().struct == Tab.intType)
			Code.loadConst(1);
		else // 0 za bool i char
			Code.loadConst(0);

	}

	// ----------------------------------------------------
	public void visit(InitListSizeExpr expr) {
		// **** trenutno zanemarujem proveru broja elem. inic liste vs broj elem niza
		// ************
		// imamo broj elem. liste na steku pa mozemo da alociramo prostor za njih
		Code.put(Code.newarray);
		if (expr.getType().struct == Tab.intType)
			Code.loadConst(1);
		else // 0 za bool i char
			Code.loadConst(0);
		// na steku je sada adresa niza; mi upisujemo elemente sledece; setujemo brojac
		// ovde
		currElem = 0;
	}

	public void visit(InitExpr expr) {
		// ovo su pojedinacni izrazi u inicijalizatorskoj listi
		// sve sto treba je na steku, sad samo cuvamo
		if (expr.getExpr().struct.getKind() == Struct.Int) {
			Code.put(Code.astore);
		} else {
			Code.put(Code.bastore);
		}
	}
	
	public void visit(InitExprs exprs) {
		// ovo su pojedinacni izrazi u inicijalizatorskoj listi
		// sve sto treba je na steku, sad samo cuvamo
		if (exprs.getExpr().struct.getKind() == Struct.Int) {
			Code.put(Code.astore);
		} else {
			Code.put(Code.bastore);
		}
	}
	
	public void visit(OperatorNewInitList opNew) {
		// niz je vec sacuvan.
	}

	public void visit(SetUp setup) {
		// ovo su pojedinacni izrazi u inicijalizatorskoj listi
		// kopiramo adresu na vrhu steka
		Code.put(Code.dup);
		// stavimo index na stek
		Code.loadConst(currElem++);
		// sad ovde treba da ide vrednost koja se upisuje
	}

	// ----------------------------------------------------

	public void visit(DesProcCall procCallStatement) {
		Obj o = procCallStatement.getDesignator().obj;
		int dest_adr = o.getAdr() - Code.pc; // racunanje relativne adrese
		Code.put(Code.call);
		Code.put2(dest_adr);
		if (o.getType() != Tab.noType)
			Code.put(Code.pop); // rezultat poziva nece biti koriscen
	}

	public void visit(DesFuncCall funcCallStatement) {
		// ukoliko je neka od predefinisanih metoda prosto ovde uradimo sta se trazi
		if (funcCallStatement.getDesignator().obj.getName().equals("len")) {
			// adresa niza je na steku
			Code.put(Code.arraylength);
			// sad je rezultat na steku
			return;
		} else if (funcCallStatement.getDesignator().obj.getName().equals("chr")) {
			// chr - konverzija int to char; int je na steku
			// sad je rezultat na steku
			return;
		} else if (funcCallStatement.getDesignator().obj.getName().equals("ord")) {
			// char to int; char je na steku
			// kao int, tako da je to to
			// sad je rezultat na steku
			return;

		}

		Obj o = funcCallStatement.getDesignator().obj;
		int dest_adr = o.getAdr() - Code.pc; // racunanje relativne adrese
		Code.put(Code.call);
		Code.put2(dest_adr);
		if (o.getType() != Tab.noType)
			Code.put(Code.pop); // rezultat poziva nece biti koriscen

	}

	// ----------------- print i read ---------------------

	public void visit(ReadStmt readStmt) {
		Obj o = readStmt.getDesignator().obj;
		Code.put(Code.read);
		// ako je niz radimo astore
		if (o.getType().getKind() == Struct.Array) {
			if (o.getType().getElemType().getKind() == Struct.Int) {
				Code.put(Code.astore);
			} else {
				Code.put(Code.bastore);
			}
		} else {
			Code.store(o);
		}
	}

	public void visit(PrintStmt print) {
		Struct t = print.getExpr().struct;
		if (t == Tab.intType) {
			Code.loadConst(5); // sirina ispisa na e-stek, expr je vec na e-steku
			Code.put(Code.print);
		} else {
			Code.loadConst(5); // sirina ispisa na e-stek, expr je vec na e-steku
			Code.put(Code.bprint);
		}
	}

	public void visit(PrintFormatStmt print) {
		// na steku su vec i expr i sirina ispisa
		Struct t = print.getExpr().struct;
		if (t == Tab.intType) {
			Code.put(Code.print);
		} else {
			Code.put(Code.bprint);
		}
	}

	public void visit(PrintNumCons cons) {
		Obj o = new Obj(Obj.Con, "", Tab.intType);
		o.setAdr(cons.getNum());
		Code.load(o);
	}

	// -------------------------------------------------

	public void visit(AddExpr AddExpr) {
		char operation = operations.pop();
		if (operation == '+')
			Code.put(Code.add);
		else if (operation == '-')
			Code.put(Code.sub);
	}

	public void visit(MulopFactor fac) {
		char operation = operations.pop();
		if (operation == '*')
			Code.put(Code.mul);
		else if (operation == '/')
			Code.put(Code.div);
		else
			Code.put(Code.rem);
	}

	public void visit(PlusOp op) {
		operations.push('+');
	}

	public void visit(MinusOp op) {
		operations.push('-');
	}

	public void visit(TimesOp op) {
		operations.push('*');
	}

	public void visit(DivOp op) {
		operations.push('/');
	}

	public void visit(ModOp op) {
		operations.push('%');
	}

	public void visit(MinusTerm minusTerm) {
		Code.put(Code.neg);
	}

	// -------------------- conditioni i relop -----------------

	Stack<Integer> orJmpStack = new Stack<Integer>();
	Stack<Integer> andJmpStack = new Stack<Integer>();
	Stack<Integer> ifForJmpStack = new Stack<Integer>(); // ako preskacemo if ili for
	Stack<Integer> elseJmpStack = new Stack<Integer>(); // ako preskacemo else
	Stack<Integer> forCondStack = new Stack<Integer>(); // pocetak conditiona
	Stack<Integer> forExitStmtStack = new Stack<Integer>(); // pocetak naredbe na kraju
	Stack<Integer> forBodyStackPatch = new Stack<Integer>(); // mesto gde patchujemo za ovo!! (ne pocetak bodyja!)
	Stack<Integer> forBodyStack = new Stack<Integer>(); // mesto gde pocinje body!

	Stack<Boolean> condExistsStack = new Stack<Boolean>();
	Stack<Boolean> exitStmtExistsStack = new Stack<Boolean>();

	Stack<ArrayList<Integer>> breakStack = new Stack<ArrayList<Integer>>();
	// Stack<ArrayList<Integer>> continueStack = new Stack<ArrayList<Integer>>();

	boolean condMet = false; // kad se skace postavimo ovo na true

	// -------------------------- if --------------------------------
	public void visit(UnmatchedIf cond) {
		// ovde patchujemo if
		Code.fixup(ifForJmpStack.pop());
	}

	public void visit(Else cond) {
		// ukoliko smo bili u if, preskacemo else
		elseJmpStack.push(Code.pc + 1);
		Code.putJump(0);

		// ovde patchujemo if
		Code.fixup(ifForJmpStack.pop());
	}

	// na ova dva mesta patchujemo else
	public void visit(UnmatchedIfElse cond) {
		Code.fixup(elseJmpStack.pop());
	}

	public void visit(IfElseStmt cond) {
		Code.fixup(elseJmpStack.pop());
	}

	// ---------------------- for -------------------------------------

	public void visit(ForBeginStmt stmt) {
		// postojao begin statement ili ne
		// ovde se skace posle izvrsavanja da bi se uradila provera uslova
		forCondStack.push(Code.pc);
		// ovde ulazimo na pocetku (ili dole)
		ArrayList<Integer> breakPatches = new ArrayList<Integer>();
		breakStack.push(breakPatches); // kad se pojavi break popujemo ovo i ubacimo novu vrednost
	}

	public void visit(ForBeginNoStmt stmt) {
		// postojao begin statement ili ne
		// ovde se skace posle izvrsavanja da bi se uradila provera uslova
		forCondStack.push(Code.pc);
		// ovde ulazimo na pocetku (ili gore)
		ArrayList<Integer> breakPatches = new ArrayList<Integer>();
		breakStack.push(breakPatches); // kad se pojavi break popujemo ovo i ubacimo novu vrednost
	}

	// uslov ne postoji
	public void visit(ForNoCond cond) {
		condExistsStack.push(false);

		// skacemo na izvrsavanje tela (kad nema exit stmt ne mora da se skace ali mi to
		// ovde ne znamo****)
		forBodyStackPatch.push(Code.pc + 1);
		Code.putJump(0);

		// ovo zapamtimo kao adr na koju se vracamo da uradimo exit statement
		forExitStmtStack.push(Code.pc);
	}

	// uslov postoji
	public void visit(ForCond cond) {
		condExistsStack.push(true);

		// ovo zapamtimo kao adr na koju se vracamo da uradimo exit statement
		forExitStmtStack.push(Code.pc);
	}

	public void visit(ForEndStmt stmt) {
		exitStmtExistsStack.push(true);
		// postojao ili ne exit statement mi skacemo gore na proveru uslova
		// kad nema uslova ovo samo nastavi jer je body u produzetku
		if (condExistsStack.peek())
			Code.putJump(forCondStack.peek());

		// svi orovi koji su ispunjeni skacu na izvrsavanje programa koje ovde pocinje
		// pisemo ovo ovde umesto u for condition
		// ako je postojao uslov patchujemo to, ako nije patchujemo deo za skok kad
		// uslova nema
		if (!orJmpStack.empty()) {
			while (!orJmpStack.empty()) {
				Code.fixup(orJmpStack.pop());
			}
		} else
			Code.fixup(forBodyStackPatch.pop());

		// mesto gde pocinje body
		forBodyStack.push(Code.pc);
	}

	public void visit(ForNoEndStmt stmt) {
		exitStmtExistsStack.push(false);
		// postojao ili ne exit statement mi skacemo gore na proveru uslova
		// kad nema uslova ovo samo nastavi jer je body u produzetku
		// if (condExistsStack.peek())
		// Code.putJump(forCondStack.peek());

		if (!orJmpStack.empty()) {
			while (!orJmpStack.empty()) {
				Code.fixup(orJmpStack.pop());
			}
		} else // no cond
			Code.fixup(forBodyStackPatch.pop());

		// mesto gde pocinje body
		forBodyStack.push(Code.pc);
	}

	public void visit(ForStmt forstmt) {
		// skacemo na exit instrukciju ako postoji
		if (exitStmtExistsStack.pop())
			Code.putJump(forExitStmtStack.peek());
		else if (condExistsStack.peek())
			Code.putJump(forCondStack.peek());
		else
			Code.putJump(forBodyStack.peek());

		// popujemo sva tri jer nam vise ne trebaju
		forExitStmtStack.pop();
		forCondStack.pop();
		forBodyStack.pop();
		// ovde se skace ako se izlazi if for-a
		// ako nemamo condition, nemamo ni fixup
		// u cond je stavljen skok na ovo u slucaju da uslov nije ispunjen
		if (condExistsStack.pop())
			Code.fixup(ifForJmpStack.pop());

		// ako je postojao break (ili vise njih) to patchujemo ovde
		ArrayList<Integer> breaks = breakStack.pop();
		while (!breaks.isEmpty()) {
			Code.fixup(breaks.remove(0));
		}

	}

	// ------ break & continue -----------
	public void visit(BreakStmt stmt) {
		// treba da prekinemo izvrsavanje ciklusa
		ArrayList<Integer> breaks = breakStack.pop();
		breaks.add(Code.pc + 1); // pamtimo adresu koju cemo da pathujemo
		Code.putJump(0);
		breakStack.push(breaks); // vratimo niz na stek
	}

	public void visit(ContinueStmt stmt) {
		// skacemo na exit stmt ako postoji, ako ne skacemo na pocetak tela
		if (exitStmtExistsStack.peek()) {
			Code.putJump(forExitStmtStack.peek());
		} else {
			Code.putJump(forBodyStack.peek());
		}
	}

	// ---------------------------------------------------------------------

	public void visit(Condition cond) {
		// ovo je poslednja klasa koja se obilazi
		// ako nije ispunjen ni jedan or preskace se if ILI FOR ispod
		ifForJmpStack.push(Code.pc + 1);
		Code.putJump(0); // posle cemo patchovati!

		// svi or jmp-ovi treba da skacu ovde ako smo u if-u, ali ako smo u foru skace
		// se na telo funkcije
		// pa to postavljamo na drugom mestu
		if (cond.getParent().getClass() != ForCond.class) {
			while (!orJmpStack.empty()) {
				Code.fixup(orJmpStack.pop());
			}
		}
	}

	// OR
	public void visit(CondTermList cond) {
	}

	public void visit(CondTerm cond) {
	}

	public void visit(CondTerms cond) {
		// ideja je da kad prodjemo ceo and iskocimo iz provere uslova ako nismo pre
		// toga iskakali
		// ako nismo ni jednom iskocili to znaci da je ovaj uslov ispunjen i da mozemo
		// da iskocimo iz or-a

		// problem je sto i kad smo u or mi ulazimo ovde, ne samo kad zavrsimo sa
		// and-ovima
		if (!andJmpStack.empty()) { // ako smo ovde dosli iz and-a radi ovo!
			orJmpStack.push(Code.pc + 1);
			Code.putJump(0); // posle cemo da patchujemo adresu
		}
		// ovde da patchujemo and-ove
		while (!andJmpStack.empty()) {
			Code.fixup(andJmpStack.pop());
		}
	}

	// AND
	public void visit(CondFactList cond) {
		// ovde sigurno imamo and
		putFalseJump(relOp);
	}

	public void visit(CondFact cond) {
		// ovo moze biti deo AND operacije, a moze biti i deo OR operacije
		// roditelj svakom simpleCondFactu i ComplexCondFactu je ovo
		if (cond.getParent().getClass() == CondFactList.class) {
			// and
			putFalseJump(relOp);
		} else if (cond.getParent().getClass() == CondTerms.class) {
			// or
			putJump(relOp);
		}
	}

	public void visit(SimpleCondFact cond) {
		// slucaj kada nemamo izraz vec samo jedan boolean
		Code.put(Code.const_1);
		relOp = "==";
		// ovo moze biti deo AND operacije, a moze biti i deo OR operacije
		// Code.putFalseJump(Code.ne, 0);

	}

	// expr relop expr
	public void visit(ComplexCondFact cond) {
		// if (cond.getParent().getClass() == CondFactList.class
		// || cond.getParent().getParent().getClass() == CondFactList.class) {
		// nalazi se u and izrazu i radimo false jmp ako uslov nije ispunjen*/
	}

	// rep ops
	public void visit(ReqOp op) {
		relOp = "==";
	}

	public void visit(NeqOp op) {
		relOp = "!=";
	}

	public void visit(GrtOp op) {
		relOp = ">";
	}

	public void visit(GrteqOp op) {
		relOp = ">=";
	}

	public void visit(LssOp op) {
		relOp = "<";
	}

	public void visit(LsseqOp op) {
		relOp = "<=";
	}

	// ------------------------------------------------------

	// skace ako nije ispunjen relOp uslov
	private void putFalseJump(String relOp) {
		andJmpStack.push(Code.pc + 1);
		switch (relOp) {
		case "==":
			Code.putFalseJump(Code.eq, 0);
			break;
		case "!=":
			Code.putFalseJump(Code.ne, 0);
			break;
		case ">":
			Code.putFalseJump(Code.gt, 0);
			break;
		case ">=":
			Code.putFalseJump(Code.ge, 0);
			break;
		case "<":
			Code.putFalseJump(Code.lt, 0);
			break;
		case "<=":
			Code.putFalseJump(Code.le, 0);
			break;
		}
	}

	// skace se ako je uslov ispunjen
	private void putJump(String relOp) {
		orJmpStack.push(Code.pc + 1);
		switch (relOp) {
		case "==":
			Code.putFalseJump(Code.ne, 0);
			break;
		case "!=":
			Code.putFalseJump(Code.eq, 0);
			break;
		case ">":
			Code.putFalseJump(Code.le, 0);
			break;
		case ">=":
			Code.putFalseJump(Code.lt, 0);
			break;
		case "<":
			Code.putFalseJump(Code.ge, 0);
			break;
		case "<=":
			Code.putFalseJump(Code.gt, 0);
			break;
		}
	}

}
