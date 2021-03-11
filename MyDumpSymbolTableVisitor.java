package rs.ac.bg.etf.pp1;

import rs.etf.pp1.symboltable.concepts.*;
import rs.etf.pp1.symboltable.visitors.DumpSymbolTableVisitor;

public class MyDumpSymbolTableVisitor extends DumpSymbolTableVisitor {

	public void visitStructNode(Struct structToVisit) {
		super.visitStructNode(structToVisit);

		switch (structToVisit.getKind()) {
		case Struct.Bool:
			output.append("bool");
			break;
		case Struct.Enum:
			output.append("enum {");
			for (Obj obj : structToVisit.getMembers()) {
				output.append("[");
				obj.accept(this);
				output.append("]");
			}
			output.append("}");
			break;
		default:
			break;
		}

	}
}
