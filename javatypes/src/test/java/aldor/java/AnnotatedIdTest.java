package aldor.java;

import aldor.typelib.AnnotatedId;
import aldorlib.sexpr.Symbol;
import org.junit.Test;

public class AnnotatedIdTest {

    @Test
    public void testAnnotatedId() {
        AnnotatedId id = AnnotatedId.newAnnotatedId(null, Symbol._MINUS_("hello"));

    }
}
