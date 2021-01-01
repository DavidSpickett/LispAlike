#!/usr/bin/python3
import argparse
import sys
from subprocess import check_output, CalledProcessError, PIPE

parser = argparse.ArgumentParser(description='Test example programs')
parser.add_argument('testfiles', metavar='file', type=str, nargs='+',
                    help='Files to test')

def check_program(program):
    check_lines = []
    with open(program, 'r') as f:
        for line in f.readlines():
            if line.startswith("##"):
                check_lines.append(
                    line.split(' ', maxsplit=1)[1])

    try:
        res = check_output(["cargo", "run", "--quiet", program],
                  universal_newlines=True, stderr=PIPE)
    except CalledProcessError as e:
        return (program, False,
            "Program failed to run. stderr:\n{}".format(e.stderr))

    if check_lines:
        expected = "".join(check_lines)
    else:
        # Just make sure it didn't crash
        expected = res

    same = expected == res
    report = ""
    if not same:
        report = "Expected:\n{}\nGot:\n{}".format(
            expected, res)
        for l1, l2 in zip(expected.splitlines(), res.splitlines()):
            if l1 != l2:
                report += "\n".join([
                    "Difference begins here -",
                    "Expected: {}".format(l1),
                    "     Got: {}".format(l2)])
                break

    return (program, same, report)

if __name__ == "__main__":
    args = parser.parse_args()

    results = []
    for f in args.testfiles:
        results.append(check_program(f))

    exit_code = 0

    for program, passed, report in results:
        print("===============================")
        print("{}:".format(program))
        if passed:
            print("PASSED".format(program))
        else:
            print(report)
            print("FAILED".format(program))
            exit_code = 1

    sys.exit(exit_code)
