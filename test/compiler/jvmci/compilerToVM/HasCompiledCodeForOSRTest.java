/*
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

/**
 * @test
 * @bug 8136421
 * @requires (os.simpleArch == "x64" | os.simpleArch == "sparcv9") & os.arch != "aarch64"
 * @library /testlibrary /../../test/lib /
 * @compile ../common/CompilerToVMHelper.java
 * @build sun.hotspot.WhiteBox
 * @run main ClassFileInstaller sun.hotspot.WhiteBox
 *                              sun.hotspot.WhiteBox$WhiteBoxPermission
 *                              jdk.vm.ci.hotspot.CompilerToVMHelper
 * @run main/othervm -XX:+UnlockExperimentalVMOptions -XX:+EnableJVMCI
 *      -XX:+UnlockDiagnosticVMOptions -XX:+WhiteBoxAPI -Xbootclasspath/a:.
 *      -XX:-BackgroundCompilation
 *      compiler.jvmci.compilerToVM.HasCompiledCodeForOSRTest
 */

package compiler.jvmci.compilerToVM;

import compiler.jvmci.common.CTVMUtilities;

import java.lang.reflect.Executable;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import compiler.testlibrary.CompilerUtils;
import jdk.vm.ci.hotspot.HotSpotResolvedJavaMethodImpl;
import jdk.vm.ci.hotspot.CompilerToVMHelper;
import jdk.test.lib.Asserts;
import sun.hotspot.WhiteBox;
import sun.hotspot.code.NMethod;

public class HasCompiledCodeForOSRTest {
    public static void main(String[] args) {
        List<CompileCodeTestCase>testCases = createTestCases();
        testCases.forEach(HasCompiledCodeForOSRTest::runSanityTest);
    }

    public static List<CompileCodeTestCase> createTestCases() {
        List<CompileCodeTestCase> testCases = new ArrayList<>();

        try {
            Class<?> aClass = DummyClass.class;
            testCases.add(new CompileCodeTestCase(
                    aClass.getMethod("withLoop"), 17));
        } catch (NoSuchMethodException e) {
            throw new Error("TEST BUG : " + e.getMessage(), e);
        }
        return testCases;
    }

    private static void runSanityTest(CompileCodeTestCase testCase) {
        System.out.println(testCase);
        Executable aMethod = testCase.executable;
        HotSpotResolvedJavaMethodImpl method = CTVMUtilities
                .getResolvedMethod(aMethod);
        testCase.deoptimize();
        int[] levels = CompilerUtils.getAvailableCompilationLevels();
        // not compiled
        for (int level : levels) {
            boolean isCompiled = CompilerToVMHelper.hasCompiledCodeForOSR(
                    method, testCase.bci, level);
            Asserts.assertFalse(isCompiled, String.format(
                    "%s : unexpected return value for non-compiled method at "
                            + "level %d", testCase, level));
        }
        NMethod nm = testCase.compile();
        if (nm == null) {
            throw new Error(String.format(
                    "TEST BUG : %s : cannot compile method", testCase));
        }

        boolean isCompiled;
        int level = nm.comp_level;
        for (int i : levels) {
            isCompiled = CompilerToVMHelper.hasCompiledCodeForOSR(
                    method, testCase.bci, i);
            Asserts.assertEQ(isCompiled, level == i, String.format(
                    "%s : unexpected return value for compiled method at "
                            + "level %d", testCase, i));
        }

        for (int i : new int[] {-1, +1}) {
            int bci = testCase.bci + i;
            isCompiled = CompilerToVMHelper.hasCompiledCodeForOSR(
                    method, bci, level);
            Asserts.assertFalse(isCompiled, String.format(
                    "%s : unexpected return value for compiled method at "
                            + "level %d with bci = %d ",
                    testCase, level, bci));
        }
    }
}