package aldor.java;

import aldor.typelib.AxiomInterface;
import aldor.typelib.TForm;
import foamj.Clos;
import foamj.FoamContext;
import foamj.FoamHelper;
import org.junit.Rule;
import org.junit.Test;

import java.io.File;
import java.io.InputStream;
import java.nio.file.Path;
import java.nio.file.Paths;

public class AxiomInterfaceTest {
    @Rule
    public DirectoryPresentRule directory = new DirectoryPresentRule("/home/pab/Work/fricas/build/src/algebra");

    @Test
    public void testOne() {
        FoamContext ctxt = new FoamContext();
        Clos fn = ctxt.createLoadFn("axiomshell");
        fn.call();
        FoamHelper.setContext(ctxt);

        AxiomInterface iface = AxiomInterface.create(directory.path());
        TForm tf = iface.asTForm("Integer");
        System.out.println("TForm: " + tf);
    }

}
