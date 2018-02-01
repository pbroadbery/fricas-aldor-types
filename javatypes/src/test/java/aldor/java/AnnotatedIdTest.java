package aldor.java;

import aldor.typelib.AnnotatedId;
import aldorlib.sexpr.Symbol;
import foamj.Clos;
import foamj.FoamContext;
import foamj.FoamHelper;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import static org.junit.Assert.assertNotNull;

public class AnnotatedIdTest {

    @Before
    public void before() {
        FoamContext ctxt = new FoamContext();

        Clos fn = ctxt.createLoadFn("axiomshell");
        fn.call();
        FoamHelper.setContext(ctxt);
    }


    @Test
    @Ignore("I'm sure this test is useful, but needs a valid env arg to newAnnotatedId")
    public void testAnnotatedId() {
        AnnotatedId id = AnnotatedId.newAnnotatedId(null, Symbol._MINUS_("hello"));
        assertNotNull(id);
    }
}
