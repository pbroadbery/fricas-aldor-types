package aldor.java;

import aldorlib.sexpr.Symbol;
import foamj.Clos;
import foamj.FoamContext;
import foamj.FoamHelper;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;

public class SymbolTest {

    @Before
    public void before() {
        FoamContext ctxt = new FoamContext();

        Clos fn = ctxt.createLoadFn("axiomshell");
        fn.call();
        FoamHelper.setContext(ctxt);
    }

    @Test
    public void testSymbol() {
        Symbol sym = Symbol._MINUS_("hello");

        assertEquals("hello", sym.name());
        assertSame(sym.rep(), Symbol._MINUS_("hello").rep());
    }
}
