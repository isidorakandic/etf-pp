package rs.ac.bg.etf.pp1;

import java.util.ArrayList;
import java.util.Stack;

import org.apache.log4j.Logger;

import rs.etf.pp1.symboltable.*;
import rs.etf.pp1.symboltable.concepts.*;
import rs.ac.bg.etf.pp1.ast.*;

public class SemanticAnalyzer extends VisitorAdaptor {
	boolean errorDetected = false;

	// kod deklarisanja promenljivih nam treba!
	private Struct currentType;

	// vrednost i tip trenutne konstante
	private int constValue;
	private int constType;

	// za detekciju greske da li su upareni postojanje povr. vrednosti i returna
	// (pri definiciji)
	private boolean isVoid;
	private boolean returnExists;

	// za ulancavanje promenljivih metode pri defininiciji metode (ne pozivu)
	private Obj currentMethod = null;

	// za enume se pamti do kog se broja stiglo
	private int nextEnumValue;

	// za proveru da li ident pripada enumu pri pristupu
	Obj currentEnum = null;

	// za relop i nizove
	private boolean goodForArray;

	// nivo ugnjezdjenja
	// int currentLevel = 0;

	// menjacemo polje fpPos objekta kad se pristupa nizu, ne elementu niza nego
	// referenci
	private static final int arrayRef = 333;

	// za ugnjezdjene pozive funkcija
	private Stack<ArrayList<Struct>> stack = new Stack<ArrayList<Struct>>();
	private Stack<Integer> currActPar = new Stack<Integer>();

	// indikator za slucaj da se u inicijalizatorskoj listi za niz pojavljuje element bas tog niza
	// tu je problem to sto se prvo obradi designator koji je ref na niz i postavi se fpPos na arrayRef
	// tako da onda kad se dohvata obj niza iz Tab fpPos == arrayRef iako se pristupa elementu niza
	// indikator se postavlja na true kad se dodje do elementa niza, a DesAsign ga cita i ako je true vraca
	// fpPos na arrayRef
	private boolean ind = false;
	
	// provera velicine inicijalizatorske liste vs velicine niza ako je zadat kao broj!
	private int lastNum; // pamti svaki broj
	private int arraySize; // ovo azuriramo u InitListSizeExpr
	private int currElem; // naredni element za upis u inicijalizatorsku listu
	
	// *************************************
	Logger log = Logger.getLogger(getClass());

	public SemanticAnalyzer() {
		System.out.println("=====================SINTAKSNA ANALIZA=========================");
	}

	public void report_error(String message, SyntaxNode info) {
		errorDetected = true;
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0 : info.getLine();
		if (line != 0)
			msg.append(" na liniji ").append(line);
		// javimo testu da je bilo greske!
		log.error(msg.toString());
	}

	public void report_info(String message, SyntaxNode info) {
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0 : info.getLine();
		if (line != 0)
			msg.append(" na liniji ").append(line);
		log.info(msg.toString());
	}
	// *************************************

	public void visit(ProgramName ProgramName) {
		// P_name je IDENT, a to je String, tako da ovo vraca String
		String name = ProgramName.getP_name();
		// ovde zapamtimo objektni cvor koji dodajemo u tabelu da bi u njega mogli da
		// ulancamo scope na kraju
		ProgramName.obj = Tab.insert(Obj.Prog, name, Tab.noType);
		Tab.openScope();

	}

	public void visit(Program Program) {
		// sve klase koje se naprave su tipa syntax node!
		// neterminalu takodje mozemo da dodelimo tip
		// u ovom slucaju neterminalu prog_name dodelimo vrednost Obj
		// i onda iz programa dohvatimo prog_name i iz njega obj koji postavimo u chain
		// local symbols

		// ovo je poslednji cvor koji se obilazi tako da cemo ovde da proverimo da li je
		// def metoda main!
		if (Tab.find("main") == Tab.noObj) {
			report_error("Greska na liniji : " + Program.getLine() + " nije definisana funkcija main!", null);
		}

		Obj program = Program.getProg_name().obj;
		Tab.chainLocalSymbols(program);
		// Tab.closeScope(); treba nam i u code generatoru
	}

	// *************** tip ************
	public void visit(Type type) {
		// type je samo neki identifikator. moramo da proverimo da li je to zapravo neki
		// tip
		Obj obj = Tab.find(type.getType_name());
		if (obj == Tab.noObj) {
			// nije nasao nista u tabeli simbola sto se tako zove
			type.struct = Tab.noType;
			report_error(
					"Greska na liniji " + type.getLine() + " : ime " + type.getType_name() + " nije u tabeli simbola",
					null);

		} else {
			// nasao je nesto, ali to ne mora da znaci da je pravi tip
			// Obj.Type je samo imenovana konstanta
			if (obj.getKind() == Obj.Type) {
				// sve je validno, jeste u pitanju neki tip i mi sad u struct type upisemo koji
				// je tip u pitanju
				type.struct = obj.getType();
			} else {
				type.struct = Tab.noType;
				report_error("Greska na liniji " + type.getLine() + " : ime " + type.getType_name()
						+ " nije odgovarajuceg tipa", null);
			}
		}
		currentType = type.struct; // da bi promenljive znale na sta da se zakace
	}

	// deklarisanje promenljivih
	public void visit(Var var) {
		// ne smeju da postoje dve promenljive sa istim imenom!
		if (Tab.currentScope.findSymbol(var.getVarName()) != null) {
			report_error(
					"Greska na liniji " + var.getLine() + ": visestruka deklaracija promenljive " + var.getVarName(),
					null);
		}
		// dodajemo novi objektni cvor u tabelu simbola
		// *** ovo moze biti i promenljiva tipa enum ***
		// sad ne moze da se vrsi provera da li je dodela vrednosti enumu validna *** !
		Struct varType = currentType;
		if (currentType == Compiler.enumStruct) {
			varType = Tab.intType;
		}
		Tab.insert(Obj.Var, var.getVarName(), varType);
		report_info("Pronadjena deklaracija promenljive " + var.getVarName() + " na liniji " + var.getLine(), null);
	}

	// deklarisanje niza
	public void visit(VarArray varArray) {
		// ne smeju da postoje dve promenljive sa istim imenom!
		if (Tab.currentScope.findSymbol(varArray.getVarName()) != null) {
			report_error("Greska na liniji " + varArray.getLine() + ": visestruka deklaracija promenljive "
					+ varArray.getVarName(), null);
		}
		// koristimo nase strukturne cvorove za nizove
		Tab.insert(Obj.Var, varArray.getVarName(), Compiler.arrayOf(currentType.getKind()));
		report_info("Pronadjena deklaracija promenljive " + varArray.getVarName() + " na liniji " + varArray.getLine(),
				null);
	}

	// deklarisanje konstanti
	// ********************************************************
	public void visit(ConstDec constDec) {
		// proveravamo da li je deklarisani tip jednak tipu koji dodeljujemo
		if (currentType.getKind() != constType) {
			report_error("Tipovi nisu komatibilni!", null);
		}
		// ne smeju da postoje dve konstante sa istim imenom!
		if (Tab.currentScope.findSymbol(constDec.getConstName()) != null) {
			report_error("Greska na liniji " + constDec.getLine() + ": visestruka definicija konstante "
					+ constDec.getConstName(), null);
		}
		Obj obj = Tab.insert(Obj.Con, constDec.getConstName(), currentType);
		obj.setAdr(constValue);
		report_info("Pronadjena definicija konstante " + constDec.getConstName() + " na liniji " + constDec.getLine(),
				null);
	}

	public void visit(InitNum initNum) {
		// ovde samo pamtimo vrednost koju cemo obraditi u ConstDec cvoru
		constValue = initNum.getNumValue();
		constType = Struct.Int;
	}

	public void visit(InitChar initChar) {
		constValue = Character.getNumericValue(initChar.getCharValue());
		constType = Struct.Char;
	}

	public void visit(InitBool initBool) {
		constValue = (initBool.getBoolValue() ? 1 : 0);
		constType = Struct.Bool;
	}

	// **************** enum *************************************

	public void visit(EnumName enumName) {
		// ne sme da postoji nesto drugo sa istim imenom!
		if (Tab.currentScope.findSymbol(enumName.getEnumName()) != null) {
			report_error("Greska na liniji " + enumName.getLine() + ": visestruka definicija enuma "
					+ enumName.getEnumName(), null);
		}

		// pravimo novi struct za svaki enum jer ce svaki imati razlicite elemente
		// da li zaista ima smisla praviti novi struct?? *******
		nextEnumValue = 0;
		enumName.obj = Tab.insert(Obj.Type, enumName.getEnumName(), Compiler.enumStruct); // promena *******
		Tab.openScope(); // zbog provere vrednosti enuma, da se ne ponavljaju i to sve...
	}

	public void visit(EnumDeclaration enumDeclaration) {
		Tab.chainLocalSymbols(enumDeclaration.getEnum_name().obj);
		Tab.closeScope();
	}

	public void visit(EnumDec enumDec) {
		// pravimo novi obj cvor sa ovim imenom i sledecom podrazumevanom vrednoscu
		// provera da li konstanta sa tom vrednoscu vec postoji
		for (Obj obj : Tab.currentScope.values()) {
			if (obj.getAdr() == nextEnumValue) {
				report_error(
						"Greska na liniji " + enumDec.getLine() + " : ne mogu dva polja enuma da imaju iste vrednosti!",
						null);
				break;
			}
		}
		Tab.insert(Obj.Con, enumDec.getEnumName(), Tab.intType).setAdr(nextEnumValue++);
	}

	public void visit(EnumDecInit enumDecInit) {
		for (Obj obj : Tab.currentScope.values()) {
			if (obj.getAdr() == enumDecInit.getEnumValue()) {
				report_error("Ne mogu dva polja enuma da imaju iste vrednosti!", null);
				break;
			}
		}
		Tab.insert(Obj.Con, enumDecInit.getEnumName(), Tab.intType).setAdr(enumDecInit.getEnumValue());
		nextEnumValue = enumDecInit.getEnumValue() + 1;

	}

	// deklarisanje metoda
	// ***********************************************************
	public void visit(RetType retType) {
		// provera! ako je ime metode main to ne moze jer main mora biti void!
		if (retType.getId().equals("main")) {
			report_error("Main mora biti void!", null);

		}
		// u retType cvoru se pamti i ime metode
		currentMethod = Tab.insert(Obj.Meth, retType.getId(), retType.getType().struct);
		currentMethod.setLevel(0);

		retType.obj = currentMethod; // ovo dodala zbog generisanja koda. treba da postavim adresu metode
		Tab.openScope();
		isVoid = false;
		returnExists = false;
	}

	public void visit(VoidRetType voidRetType) {
		// u voidRetType cvoru se pamti i ime metode
		currentMethod = Tab.insert(Obj.Meth, voidRetType.getId(), Tab.noType);
		currentMethod.setLevel(0);
		voidRetType.obj = currentMethod; // ovo dodala zbog generisanja koda. treba da postavim adresu objekta
		Tab.openScope();
		isVoid = true;
		returnExists = false;
	}

	public void visit(MethodDec methodDec) {
		// provara uparednosti returna i void
		if (isVoid && returnExists) {
			report_error("Greska na liniji " + methodDec.getLine() + " : metoda je void a postoji povratna vrednost!",
					null);
		}
		if (!isVoid && !returnExists) {
			report_error(
					"Greska na liniji " + methodDec.getLine() + " : metoda nije void a ne postoji povratna vrednost!",
					null);
		}

		// main mora da nema parametara!
		if (currentMethod.getName().equals("main") && currentMethod.getLevel() != 0) {
			report_error("Greska na liniji: " + methodDec.getLine() + ": main metoda ne sme imati parametre!", null);
		}

		// na kraju zatvaramo current scope
		// u CloseScopeClass smo ulancali simbole nakon deklaracije promenljivih 
		Tab.closeScope();
	}

	// ********* formalni parametri metode **************
	public void visit(ScalarPar par) {
		int numOfPars = currentMethod.getLevel();
		// pravimo novi objektni cvor i postavljamo redni broj parametra (idu od 0)
		// ************** ovo moze biti i enum i u tom slucaju necemo da njegov tip bude
		// enum vec int! ******
		if (currentType.getKind() == Struct.Enum)
			currentType = Tab.intType;
		Tab.insert(Obj.Var, par.getId(), currentType).setFpPos(numOfPars);
		currentMethod.setLevel(numOfPars + 1);
	}

	public void visit(ArrayPar par) {
		int numOfPars = currentMethod.getLevel();
		// pravimo novi objektni cvor i postavljamo redni broj parametra (idu od 0)
		Struct type = Compiler.arrayOf(currentType.getKind());
		Tab.insert(Obj.Var, par.getId(), type).setFpPos(numOfPars);
		currentMethod.setLevel(numOfPars + 1);
	}

	// ***** return iskazi ******
	public void visit(ReturnStmt returnStmt) {
		// returnExists je vec na false;
	}

	public void visit(ReturnExprStmt returnExprStmt) {
		returnExists = true;
		Struct currMethType = currentMethod.getType();
		if (!currMethType.compatibleWith(returnExprStmt.getExpr().struct)) {
			report_error("Greska na liniji " + returnExprStmt.getLine()
					+ " : tip izraza u return naredbi ne slaze se sa tipom povratne vrednosti funkcije "
					+ currentMethod.getName(), null);
		}
	}

	// ************** obrada izraza ********************

	// ******* expr, term i factor *************

	// provera parametara pri pozivu funkcije ce ovde da se radi!
	// u ovo se ulazi samo pri pozivu funkcije
	public void visit(Expression expr) {
		expr.struct = expr.getExpr().struct;
		// proveravamo element koji je na redu iz liste sa vrha steka
		ArrayList<Struct> currList = null;
		if (!stack.isEmpty()) {
			currList = stack.pop(); // lista formalnih argumenata f-je koja se poziva
		}
		int index = Integer.MAX_VALUE;
		if (!currActPar.isEmpty()) {
			index = currActPar.pop(); // broj dosad obradjenih parametara
		}

		Struct currParametar = null;
		if (currList != null && currList.size() > index) {
			currParametar = currList.get(index); // uzimamo onaj koji je na redu
			// provera da li se tipovi poklapaju
			if (!expr.struct.assignableTo(currParametar)) {
				report_error("Greska na liniji " + expr.getLine() + " : neodgovarajuci " + (index + 1)
						+ ". parametar pri pozivu funkcije ", null);
			}
		}

		// na stek vracamo inkrementirani index da kazemo da smo obradili jedan
		// parametar
		if (currList != null)
			stack.push(currList); // currList vratimo nepromenjen
		if (index != Integer.MAX_VALUE) {
			currActPar.push(index + 1);
		}
	}

	// i ovde isto!
	// ******* prilicno sam sigurna da ovo ne radi nista, tj da je sve vec obradjeno
	// dok se ovde udje? ************
	public void visit(Expessions exprs) {
		exprs.struct = exprs.getExpr().struct;
		// proveravamo element koji je na redu iz liste sa vrha steka
		ArrayList<Struct> currList = null;
		if (!stack.isEmpty()) {
			currList = stack.pop();
		}
		int index = Integer.MAX_VALUE;
		if (!currActPar.isEmpty()) {
			index = currActPar.pop();
		}

		Struct currParametar = null;
		if (currList != null && currList.size() > index) {
			currParametar = currList.get(index); // uzimamo onaj koji je na redu
			// provera da li se tipovi poklapaju
			if (!currParametar.assignableTo(exprs.struct)) {
				report_error("Greska na liniji " + exprs.getLine() + " : neodgovarajuci " + (index + 1)
						+ ". parametar pri pozivu funkcije ", null);
			}
		}

		// na stek vracamo inkrementirani index da kazemo da smo obradili jedan
		// parametar
		if (currList != null)
			stack.push(currList); // currList vratimo nepromenjen
		if (index != Integer.MAX_VALUE)
			currActPar.push(index + 1);
	}

	public void visit(Expr expr) {
		expr.struct = expr.getTerm_list().struct;
	}

	public void visit(Term term) {
		term.struct = term.getFactor_list().struct;
	}

	public void visit(AddExpr addExpr) {
		Struct te = addExpr.getTerm_list().struct;
		Struct t = addExpr.getTerm().struct;
		if (te.equals(t) && te == Tab.intType)
			addExpr.struct = te;
		else {
			report_error("Greska na liniji " + addExpr.getLine() + " : nekompatibilni tipovi u izrazu za sabiranje.",
					null);
			addExpr.struct = Tab.noType;
		}
	}

	public void visit(TermExpr termExpr) {
		termExpr.struct = termExpr.getTerm().struct;
	}

	public void visit(SimpleFactor factor) {
		factor.struct = factor.getFactor().struct;
	}

	public void visit(MinusTerm factor) {
		factor.struct = factor.getTerm().struct;
		// provera: factor mora biti tipa int
		if (factor.struct.getKind() != Struct.Int)
			report_error("Greska na liniji " + factor.getLine() + " : faktor mora biti tipa int!", null);
	}

	public void visit(MulopFactor factor) {
		factor.struct = factor.getFactor().struct;
		// provera: oba moraju biti int
		if (factor.getFactor_list().struct.getKind() != Struct.Int || factor.struct.getKind() != Struct.Int)
			report_error("Greska na liniji " + factor.getLine() + " : oba operatora mnozenja moraju biti tipa int!",
					null);
	}

	// faktori *******
	public void visit(FuncCall funcCall) {
		Obj func = funcCall.getDesignator().obj;
		// designator treba da bude metoda
		if (Obj.Meth == func.getKind()) {
			report_info("Pronadjen poziv funkcije " + func.getName() + " na liniji " + funcCall.getLine(), null);
			funcCall.struct = func.getType();
		} else {
			report_error("Greska na liniji " + funcCall.getLine() + " : ime " + func.getName() + " nije funkcija!",
					null);
			funcCall.struct = Tab.noType;
		}
		// provera da li nam je dobar broj paremetara funkcije
		// sa steka skinemo da proverimo koliko smo parametara obradili
		int index = Integer.MAX_VALUE;
		if (!currActPar.isEmpty()) {
			index = currActPar.pop(); // broj obradjenih parametara
		}
		// popujemo sa steka jer nam svakako vise ne treba ni taj niz ni broj obradjenih
		// elemenata
		int actParsNum = -1;
		if (!stack.isEmpty()) {
			ArrayList<Struct> al = stack.pop();
			actParsNum = al.size(); // broj formalnih arg pozivane funkcije
		}
		if (actParsNum != -1 && actParsNum != index) {
			report_error(
					"Greska na liniji " + funcCall.getLine() + " : neodgovarajuci broj parametara pri pozivu funkcije ",
					null);
		}

	}

	public void visit(FuncCallNoPar funcCall) {
		Obj func = funcCall.getDesignator().obj;
		// designator treba da bude metoda
		if (Obj.Meth == func.getKind()) {
			report_info("Pronadjen poziv funkcije " + func.getName() + " na liniji " + funcCall.getLine(), null);
			funcCall.struct = func.getType();
		} else {
			report_error("Greska na liniji " + funcCall.getLine() + " : ime " + func.getName() + " nije funkcija!",
					null);
			funcCall.struct = Tab.noType;
		}
		// provera da li nam je dobar broj paremetara funkcije
		// sa steka skinemo da proverimo koliko smo parametara obradili
		int index = Integer.MAX_VALUE;
		if (!currActPar.isEmpty()) {
			index = currActPar.pop();
		}
		// popujemo sa steka jer nam svakako vise ne treba ni taj niz ni broj obradjenih
		// elemenata
		int actParsNum = -1;
		if (!stack.isEmpty()) {
			actParsNum = stack.pop().size();
		}
		if (actParsNum != -1 && actParsNum != index) {
			report_error(
					"Greska na liniji " + funcCall.getLine() + " : neodgovarajuci broj parametara pri pozivu funkcije ",
					null);
		}

	}
	
	public void visit(ParenthesisExpr expr) {
		expr.struct = expr.getExpr().struct;
	}

	public void visit(VarRef varRef) {
		// provera da li je promenljiva
		// ako je level = niz je
		// ako je obj niz i level != niz je: u struct: getElemType()
		// *************************************************************************
		Obj desObj = varRef.getDesignator().obj;
		if (desObj.getType().getKind() == Struct.Array) {
			if (desObj.getFpPos() != arrayRef) {
				// pristupa se elementu niza i u struct upisujemo elemType
				varRef.struct = desObj.getType().getElemType();
			} else {
				varRef.struct = desObj.getType();
				desObj.setFpPos(0);
			}
		} else {
			varRef.struct = desObj.getType();
		}

	}

	public void visit(IntRef intRef) {
		intRef.struct = Tab.intType;
		lastNum = intRef.getI();
	}

	public void visit(CharRef charRef) {
		charRef.struct = Tab.charType;
	}

	public void visit(BoolRef boolRef) {
		boolRef.struct = Compiler.boolStruct;
	}

	public void visit(OperatorNew operatorNew) {
		// izraz mora biti int!
		if (operatorNew.getExpr().struct.getKind() != Struct.Int) {
			report_error("Greska na liniji " + operatorNew.getLine() + " : izraz nije tipa int!", null);
		}
		operatorNew.struct = Compiler.arrayOf(operatorNew.getType().struct.getKind());
	}

	// ********* inicijalizatorske liste ******************
	
	public void visit(InitListSizeExpr expr) {
		expr.struct = expr.getExpr().struct;
		arraySize = lastNum;
		currElem = 0;
	}
	
	public void visit(OperatorNewInitList operatorNew) {
		// isti kod kao za OperatorNew 
		if (operatorNew.getSize_expr().struct.getKind() != Struct.Int) {
			report_error("Greska na liniji " + operatorNew.getLine() + " : izraz nije tipa int!", null);
		}
		operatorNew.struct = Compiler.arrayOf(operatorNew.getSize_expr().struct.getKind()); // ***** je l ovo okej??? *****
		if (currElem != arraySize) {
			report_error("Greska na liniji " + operatorNew.getLine() + " : velicina niza se ne poklapa sa brojem elementa inicijalizatorske liste!", null);
		}
	}
	
	public void visit(InitExpr initExpr) {
		// obradili jos jedan element
		currElem++;
		// jedan od izraza u inicijalizatorskoj listi
		if (initExpr.getExpr().struct != currentType) {
			report_error("Greska na liniji " + initExpr.getLine()
					+ " : element inicijalizatorske liste nije odgovarajuceg tipa!", null);
		}
	}

	public void visit(InitExprs initExpr) {
		// obradili jos jedan element
		currElem++;
		// jedan od izraza u inicijalizatorskoj listi
		if (initExpr.getExpr().struct != currentType) {
			report_error("Greska na liniji " + initExpr.getLine()
					+ " : element inicijalizatorske liste nije odgovarajuceg tipa!", null);
		}
	}

	// ********** designatori ***************

	public void visit(Designator designator) {
		designator.obj = designator.getIdent_expr_list().obj;
	}

	public void visit(SimpleDesignator designator) {
		// ako je niz level = kod.nizje
		Obj obj = Tab.find(designator.getId());
		designator.obj = obj;
		if (obj == Tab.noObj) {
			report_error(
					"Greska na liniji " + designator.getLine() + " : ime " + designator.getId() + " nije deklarisano! ",
					null);
		}
		// ovo ne sme biti enum
		// *** ali sme da bude promenljiva tipa enum - ako je kind = var onda je okej iako je enum
		if (obj.getKind() == Obj.Con && obj.getType().getKind() == Struct.Enum) {
			report_error(
					"Greska na liniji " + designator.getLine() + " : nelegalan pristup enumu " + designator.getId(),
					null);
		}

		// ***********************************************************************
		// ako je des niz, onda se pristupa referenci i u tom slucaju postavljamo level
		// na arrayRef
		if (obj.getType().getKind() == Struct.Array)
			obj.setFpPos(arrayRef);
		// ***********************************************************************

		// --------za pozive funkcija ------
		if (obj.getKind() == Obj.Meth) {
			ArrayList<Struct> actualPars = new ArrayList<Struct>();
			int i = 0;
			for (Obj o : obj.getLocalSymbols()) {
				if (i < obj.getLevel()) {
					actualPars.add(o.getType());
					i++;
				}
			}
			// ubacimo na stek
			if (actualPars != null) // mozda je funkcija bez parametara!
				stack.push(actualPars);
			// na stek stavimo i da nismo obradili ni jedan parametar
			currActPar.push(0);
		}

	}

	public void visit(ArrayIdent ident) {
		// ovo nam sluzi samo da zakacimo ime za obj
		ident.obj = new Obj(Obj.NO_VALUE, ident.getId(), Tab.noType);
	}

	// array designator
	public void visit(ArrayDesignator designator) {
		String desName = designator.getArray_ident().obj.getName();
		Obj obj = Tab.find(desName);
		designator.getArray_ident().obj = obj;
		designator.obj = obj;
		if (obj == Tab.noObj) {
			report_error("Greska na liniji " + designator.getLine() + " : ime " + desName + " nije deklarisano! ",
					null);
		}
		// provera da li je deklarisano ime zapravo niz!
		if (obj.getType().getKind() != Struct.Array) {
			report_error("Greska na liniji " + designator.getLine() + " : ime " + desName + " nije niz! ", null);
			designator.obj = obj;
		} 
		// provera da li je expr int
		if (designator.getExpr().struct != Tab.intType) {
			report_error("Greska na liniji " + designator.getLine() + " : izraz nije tipa int! ", null);
		}
		
		// ********** za ind i inicij. liste ****
		if (obj.getFpPos() == arrayRef) {
			ind = true;
			obj.setFpPos(0);
		}
	}

	public void visit(EnumDesignator designator) {
		Obj obj = Tab.find(designator.getId());
		designator.obj = Tab.noObj;
		// provera da li je ident zapravo enum!
		if (obj.getType().getKind() != Struct.Enum) {
			report_error("Greska na liniji " + designator.getLine() + " : ime " + designator.getId() + " nije enum! ",
					null);
		} else {
			// u tabeli simbola nadjemo trazeni element enuma
			for (Obj o : obj.getLocalSymbols()) {
				if (o.getName().equals(designator.getId2())) {
					designator.obj = o;
					break;
				}
			}
			if (obj == Tab.noObj) {
				report_error("Greska na liniji " + designator.getLine() + " : ime " + designator.getId()
						+ " nije deo enuma " + designator.getId(), null);
			}

		}
	}

	// dodela vrednosti
	public void visit(DesAsign desAsign) {
		if (ind) {
			desAsign.getDesignator().obj.setFpPos(arrayRef);
			ind = false;
		}
		// designator mora biti promenljiva
		if (desAsign.getDesignator().obj.getKind() != Obj.Var) {
			report_error("Greska na liniji " + desAsign.getLine() + " : ime " + desAsign.getDesignator().obj.getName()
					+ " nije promenljiva!", null);
		}
		// **************************************************************
		// provera da li dodeljujemo elementu niza vrednost
		Struct desStruct = desAsign.getDesignator().obj.getType();
		if (desStruct.getKind() == Struct.Array) {
			if (desAsign.getDesignator().obj.getFpPos() != arrayRef)
				desStruct = desStruct.getElemType();
			else
				desAsign.getDesignator().obj.setFpPos(0);
		}
		// **************************************************************
		// tipovi pri dodeli moraju biti komatibilni
		if (!desAsign.getExpr().struct.assignableTo(desStruct)) {
			report_error("Greska na liniji " + desAsign.getLine() + " : " + "nekompatibilni tipovi u dodeli vrednosti ",
					null);
		}
	}

	public void visit(DesInc desInc) {
		// designator mora biti promenljiva
		if (desInc.getDesignator().obj.getKind() != Obj.Var) {
			report_error("Greska na liniji " + desInc.getLine() + " : ime " + desInc.getDesignator().obj.getName()
					+ " nije promenljiva!", null);
		}
		// ****************************************************************************
		int kind = desInc.getDesignator().obj.getType().getKind();
		if (kind == Struct.Array) {
			if (desInc.getDesignator().obj.getFpPos() != arrayRef) {
				// pristupa se elementu niza pa cemo staviti kind ne array nego tip elementa
				kind = desInc.getDesignator().obj.getType().getElemType().getKind();
			} else {
				desInc.getDesignator().obj.setFpPos(0);
			}
		}

		// *****************************************************************************
		// designator mora biti int
		if (kind != Struct.Int) {
			report_error("Greska na liniji " + desInc.getLine() + " : ime " + desInc.getDesignator().obj.getName()
					+ " nije tipa int!", null);
		}
	}

	public void visit(DesDec desDec) {
		// designator mora biti promenljiva
		if (desDec.getDesignator().obj.getKind() != Obj.Var) {
			report_error("Greska na liniji " + desDec.getLine() + " : ime " + desDec.getDesignator().obj.getName()
					+ " nije promenljiva!", null);
		}
		// ****************************************************************************
		int kind = desDec.getDesignator().obj.getType().getKind();
		if (kind == Struct.Array) {
			if (desDec.getDesignator().obj.getFpPos() != arrayRef) {
				// pristupa se elementu niza pa cemo staviti kind ne array nego tip elementa
				kind = desDec.getDesignator().obj.getType().getElemType().getKind();
			} else {
				desDec.getDesignator().obj.setFpPos(0);
			}
		}
		// *****************************************************************************
		// designator mora biti int
		if (kind != Struct.Int) {
			report_error("Greska na liniji " + desDec.getLine() + " : ime " + desDec.getDesignator().obj.getName()
					+ " nije tipa int!", null);
		}
	}

	// poziv funkcije
	public void visit(DesFuncCall desFuncCall) {
		Obj func = desFuncCall.getDesignator().obj;
		if (Obj.Meth == func.getKind()) {
			report_info("Pronadjen poziv funkcije " + func.getName() + " na liniji " + desFuncCall.getLine(), null);
			desFuncCall.struct = func.getType();
		} else {
			report_error("Greska na liniji " + desFuncCall.getLine() + " : ime " + func.getName() + " nije funkcija!",
					null);
			desFuncCall.struct = Tab.noType;
		}
		// provera poklapanja broja i tipa agrumenata funkcije!
		// sa steka skinemo da proverimo koliko smo parametara obradili
		int index = Integer.MAX_VALUE;
		if (!currActPar.isEmpty()) {
			index = currActPar.pop();
		}
		// popujemo sa steka jer nam svakako vise ne treba ni taj niz ni broj obradjenih
		// elemenata
		int actParsNum = -1;
		if (!stack.isEmpty()) {
			actParsNum = stack.pop().size();
		}
		if (actParsNum != index) {
			report_error("Greska na liniji " + desFuncCall.getLine()
					+ " : neodgovarajuci broj parametara pri pozivu funkcije ", null);
		}

	}

	// poziv procedure
	public void visit(DesProcCall desProcCall) {
		Obj func = desProcCall.getDesignator().obj;
		if (Obj.Meth == func.getKind()) {
			report_info("Pronadjen poziv funkcije " + func.getName() + " na liniji " + desProcCall.getLine(), null);
			desProcCall.struct = func.getType();
		} else {
			report_error("Greska na liniji " + desProcCall.getLine() + " : ime " + func.getName() + " nije funkcija!",
					null);
			desProcCall.struct = Tab.noType;
		}
		// provera da li nam je dobar broj paremetara funkcije
		// sa steka skinemo da proverimo koliko smo parametara obradili
		int index = Integer.MAX_VALUE;
		if (!currActPar.isEmpty()) {
			index = currActPar.pop();
		}
		// popujemo sa steka jer nam svakako vise ne treba ni taj niz ni broj obradjenih
		// elemenata
		int actParsNum = -1;
		if (!stack.isEmpty()) {
			actParsNum = stack.pop().size();
		}
		if (actParsNum != index) {
			report_error("Greska na liniji " + desProcCall.getLine()
					+ " : neodgovarajuci broj parametara pri pozivu funkcije ", null);
		}
	}

	// ********** print, read i ostalo **********************

	public void visit(PrintStmt stmt) {
		// expr mora biti int, char ili bool
		int type = stmt.getExpr().struct.getKind();
		if (type != Struct.Bool && type != Struct.Char && type != Struct.Int) {
			report_error("Greska na liniji " + stmt.getLine() + " : izraz mora biti tipa bool, int ili char!", null);
		}
	}

	public void visit(PrintFormatStmt stmt) {
		// expr mora biti int, char ili bool
		int type = stmt.getExpr().struct.getKind();
		if (type != Struct.Bool && type != Struct.Char && type != Struct.Int) {
			report_error("Greska na liniji " + stmt.getLine() + " : izraz mora biti tipa bool, int ili char!", null);
		}
	}

	public void visit(ReadStmt stmt) {
		// des mora biti var
		if (stmt.getDesignator().obj.getKind() != Obj.Var) {
			report_error("Greska na liniji " + stmt.getLine() + " : ime " + stmt.getDesignator().obj.getName()
					+ " nije promenljiva!", null);
		}
		// ******************************************
		int type = stmt.getDesignator().obj.getType().getKind();
		if (type == Struct.Array) {
			if (stmt.getDesignator().obj.getFpPos() != arrayRef)
				type = stmt.getDesignator().obj.getType().getElemType().getKind();
			else
				stmt.getDesignator().obj.setFpPos(0);
		}
		// ******************************************
		// mora biti int, char ili bool
		if (type != Struct.Bool && type != Struct.Char && type != Struct.Int) {
			report_error("Greska na liniji " + stmt.getLine() + " : izraz mora biti tipa bool, int ili char!", null);
		}
	}

	// **************** condition *****************
	public void visit(SimpleCondFact fact) {
		// expr mora biti tipa bool
		if (fact.getExpr().struct.getKind() != Struct.Bool) {
			report_error("Greska na liniji " + fact.getLine() + " : izraz mora biti tipa bool!", null);
		}
	}

	public void visit(ComplexCondFact fact) {
		// expressioni moraju biti kompatibilni
		Struct exp1 = fact.getExpr().struct;
		Struct exp2 = fact.getExpr1().struct;
		if (!exp1.compatibleWith(exp2)) {
			report_error("Greska na liniji " + fact.getLine() + " : izrazi moraju biti komatibilni!", null);
		}
		// ako su nizovi, od operatora moze da se koristi samo != ili ==
		if (exp1.getKind() == Struct.Array && exp2.getKind() == Struct.Array) {
			if (!goodForArray) {
				report_error("Greska na liniji " + fact.getLine()
						+ " : za nizove se mogu koristiti samo relacioni operatori == i !=", null);
			}
		}
	}

	// zatvaranje scopa nakon deklaracije lokalnih promenljivih metode!
	public void visit(CloseScopeClass c) {
		Tab.chainLocalSymbols(currentMethod);
	}

	public void visit(ReqOp op) {
		goodForArray = true;
	}

	public void visit(NeqOp op) {
		goodForArray = true;
	}

	public void visit(GrtOp op) {
		goodForArray = false;
	}

	public void visit(GrteqOp op) {
		goodForArray = false;
	}

	public void visit(LssOp op) {
		goodForArray = false;
	}

	public void visit(LsseqOp op) {
		goodForArray = false;
	}

}
