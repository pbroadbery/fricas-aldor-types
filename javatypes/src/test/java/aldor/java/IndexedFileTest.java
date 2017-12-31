package aldor.java;

import aldor.typelib.IndexedFile;
import aldorlib.sexpr.SExpression;
import aldorlib.sexpr.Symbol;
import foamj.Clos;
import foamj.FoamContext;
import foamj.FoamHelper;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;

public class IndexedFileTest {
    @Rule
    public DirectoryPresentRule directory = new DirectoryPresentRule("/home/pab/Work/fricas/build/src/algebra");

    @Before
    public void before() {
        FoamContext ctxt = new FoamContext();

        Clos fn = ctxt.createLoadFn("axiomshell");
        fn.call();
        FoamHelper.setContext(ctxt);
    }


    @Test
    public void testOne() {
        IndexedFile file = new IndexedFile(directory.path() + "/LIST.NRLIB/index.KAF");
        SExpression sx = file.get(Symbol._MINUS_("abbreviation"));
        System.out.println("SX: " + sx.sym().name());
    }
}