#!/usr/bin/env python3
"""
lift_graph.py - Generate theta lifting diagrams with DRC packet annotations.

Generates a Graphviz directed graph showing the theta lifting tree for
a given partition and root system type. Each node displays the local system
and its matched DRC diagram packet.

Usage:
  python3 tools/lift_graph.py PARTITION -t TYPE [-f FORMAT] [-o OUTPUT]

Examples:
  # Type C partition (5,5,2,2), output PDF
  python3 tools/lift_graph.py 5,5,2,2 -t C

  # Type M partition, output SVG
  python3 tools/lift_graph.py 2,2,2,2,1,1 -t M -f svg

  # Type D partition, custom output filename
  python3 tools/lift_graph.py 6,4,2,2 -t D -o my_graph

  # Also print DRC diagrams
  python3 tools/lift_graph.py 5,5,2,2 -t C --print-drc

Supported types: C, D, M, B
Supported formats: pdf (default), svg, png
"""
import sys
import os
import argparse

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from combunipotent import gen_lift_graph, part2drc, dpart2drc, str_dgms, reg_drc


def parse_partition(s):
    """Parse a comma-separated string into a tuple of integers."""
    parts = []
    for x in s.replace(' ', '').split(','):
        x = x.strip()
        if x:
            parts.append(int(x))
    parts.sort(reverse=True)
    return tuple(parts)


def main():
    parser = argparse.ArgumentParser(
        description='Generate theta lifting graph with DRC packet annotations.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s 5,5,2,2 -t C              # Type C, PDF output
  %(prog)s 2,2,2,2,1,1 -t M -f svg   # Type M, SVG output
  %(prog)s 6,4,2,2 -t D -o my_graph  # Type D, custom filename
  %(prog)s 5,5,2,2 -t C --print-drc  # Also print DRC diagrams
""")

    parser.add_argument('partition', type=str,
                        help='Comma-separated partition (e.g. "5,5,2,2")')
    parser.add_argument('-t', '--type', required=True, choices=['B', 'C', 'D', 'M'],
                        help='Root system type')
    parser.add_argument('-f', '--format', default='pdf', choices=['pdf', 'svg', 'png'],
                        help='Output format (default: pdf)')
    parser.add_argument('-o', '--output', default=None,
                        help='Output filename without extension (default: lift_tree)')
    parser.add_argument('--print-drc', action='store_true',
                        help='Also print all DRC diagrams to stdout')

    args = parser.parse_args()

    part = parse_partition(args.partition)
    rtype = args.type

    print(f"Partition: {part}")
    print(f"Type: {rtype}")
    print(f"Format: {args.format}")

    # Optionally print DRC diagrams
    if args.print_drc:
        print(f"\n{'='*40}")
        print(f"DRC diagrams for type {rtype}, partition {part}:")
        print(f"{'='*40}")
        drcs = part2drc(part, rtype=rtype, report=True, printdig=False)
        for i, drc in enumerate(drcs):
            drc = reg_drc(drc)
            print(f"\n--- DRC #{i+1} ---")
            print(str_dgms(drc))
        print(f"\nTotal: {len(drcs)} DRC diagrams")

    # Generate the graph
    print(f"\nGenerating lift graph...")
    g = gen_lift_graph(part, rtype=rtype, format=args.format)

    if g is None:
        print("Error: gen_lift_graph returned None", file=sys.stderr)
        sys.exit(1)

    # For non-SVG formats, g is a Digraph object; render it
    if args.format != 'svg':
        if args.output:
            g.filename = args.output
        outfile = g.render()
        print(f"Output: {outfile}")
    else:
        # For SVG, gen_lift_graph already rendered and returned an SVG object
        if args.output:
            outfile = args.output + '.svg'
        else:
            outfile = 'lift_tree.svg'
        print(f"Output: {outfile}")


if __name__ == '__main__':
    main()
