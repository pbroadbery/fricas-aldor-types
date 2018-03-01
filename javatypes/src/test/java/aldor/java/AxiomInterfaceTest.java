package aldor.java;

import aldor.typelib.AnnotatedAbSyn;
import aldor.typelib.AxiomInterface;
import aldor.typelib.Export;
import aldor.typelib.NamedExport;
import aldor.typelib.SymbolDatabase;
import aldor.typelib.SymbolMeaning;
import aldor.typelib.TForm;
import aldor.typelib.TypePackage;
import foamj.Clos;
import foamj.FoamContext;
import foamj.FoamHelper;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class AxiomInterfaceTest {
    @Rule
    public DirectoryPresentRule directory = new DirectoryPresentRule("/home/pab/Work/fricas/opt/lib/fricas/target/x86_64-unknown-linux/algebra/");
    private AxiomInterface iface;

    @Before
    public void before() {
        FoamContext ctxt = new FoamContext();
        Clos fn = ctxt.createLoadFn("axiomshell");
        fn.call();
        FoamHelper.setContext(ctxt);
        SymbolDatabase db = SymbolDatabase.daases(directory.path());
        iface = AxiomInterface.create(db);
    }

    @Test
    public void testOne() {
        TForm tf = iface.asTForm("Integer");
        System.out.println("TForm: " + tf.toString());

        System.out.println(iface.allCatParents(tf));
    }

    @Test
    public void testInfer() {
        AnnotatedAbSyn abSyn = iface.annotated("Integer");
        TForm tf = iface.infer(abSyn);
        System.out.println("Type is: " + tf);
        System.out.println("Type is: " + iface.allCatParents(tf));
        System.out.println("Type is: " + iface.directParents(tf));
    }

    @Test
    public void testDirectParentsInt() {
        AnnotatedAbSyn abSyn = iface.annotated("Integer");
        TForm tf = iface.infer(abSyn);
        for (TForm tfi: iface.directParents(tf)) {
            System.out.println("Parent: " + tfi);
        }
        assertTrue(iface.directParents(tf).size()>0);
    }

    @Test
    public void testDirectParentsGroup() {
        TForm tf = iface.asTForm("Group");
        for (TForm tfi: iface.directParents(tf)) {
                System.out.println("Parent: " + tfi);
        }
        assertTrue(iface.directParents(tf).size()>0);
    }

    @Test
    public void testDirectParentsBasicType() {
        TForm tf = iface.asTForm("BasicType");
        for (TForm tfi: iface.directParents(tf)) {
            System.out.println("Parent: " + tfi);
        }
    }

    @Test
    public void testParentsExtensibleLinearAggregate() {
        TForm tf = iface.asTForm("(ExtensibleLinearAggregate X)");
        for (TForm tfi: iface.directParents(tf)) {
            System.out.println("Parent: " + tfi);
        }
    }


    @Test
    public void testSemiRng() {
        TForm tf = iface.asTForm("SemiRng");
        for (TForm tfi: iface.directParents(tf)) {
            System.out.println("Parent: " + tfi);
            if (tfi.toString().contains("SemiGroup")) {

                for (TForm tfij: iface.directParents(tfi)) {
                    System.out.println(" " + tfi + " -> " + tfij);
                }
            }
        }
    }

    private List<TForm> expand(TForm tf) {
        ArrayList<TForm> parents = iface.directParents(tf);
        return parents.stream().flatMap(p -> Stream.concat(Stream.of(p), (expand(p).stream()))).collect(Collectors.toList());
    }

    @Test
    public void testVectorSpace() {
        TForm tf = iface.asTForm("(VectorSpace S)");
        for (TForm ptf: expand(tf)) {
            System.out.println("Parent: " + ptf);
        }
    }

    @Test
    public void testOperations() {
        AnnotatedAbSyn absyn = iface.annotated("(List Integer)");

        ArrayList<NamedExport> directOperations = iface.directOperations(absyn);
        for (NamedExport syme: directOperations) {
            System.out.println("type: " + syme.name() + " " + syme.type().sexpression());
            System.out.println("orig: " + syme.name() + " " + syme.original().sexpression());
        }

    }

    @Test
    public void testAllTypes() {
        ArrayList<AnnotatedAbSyn> allTypes = iface.allTypes();
        assertFalse(allTypes.stream().map(AnnotatedAbSyn::toString).anyMatch(s -> s.contains("Ring&")));
        assertFalse(allTypes.isEmpty());
    }

}

