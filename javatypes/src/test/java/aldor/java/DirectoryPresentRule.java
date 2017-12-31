package aldor.java;

import org.junit.Assume;
import org.junit.rules.TestRule;
import org.junit.runner.Description;
import org.junit.runners.model.Statement;

import java.io.File;

class DirectoryPresentRule implements TestRule {
    private final String path;

    DirectoryPresentRule(String path) {
        this.path = path;
    }

    @Override
    public Statement apply(Statement statement, Description description) {
        File executable = new File(path);
        Assume.assumeTrue(executable.isDirectory());

        return statement;
    }

    public String path() {
        return path;
    }
}
