const std = @import("std");
const zigimg = @import("zigimg");

const dim: usize = 256;

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    var scratch = arena.allocator();

    const args: [][*:0]u8 = std.os.argv;
    if (args.len != 4) {
        usage(args[0]);
        return;
    }

    const exe_path = try std.fs.selfExeDirPathAlloc(scratch);
    defer scratch.free(exe_path);

    const png_data: []u8 = try scratch.alloc(u8, 3 * dim * dim);
    defer scratch.free(png_data);

    if (CheckArg.isNaive()) {
        if (CheckArg.orientTest()) {
            Orient2DTests(f64).run(false, png_data);
        } else if (CheckArg.circleTest()) {
            std.debug.print("not yet implemented\n", .{});
            return;
        } else {
            usage(args[0]);
            return;
        }
    } else if (CheckArg.isRobust()) {
        if (CheckArg.orientTest()) {
            Orient2DTests(f64).run(true, png_data);
        } else if (CheckArg.circleTest()) {
            std.debug.print("not yet implemented\n", .{});
            return;
        } else {
            usage(args[0]);
            return;
        }
    } else {
        usage(args[0]);
        return;
    }

    const file_name = std.os.argv[3][0..std.mem.len(std.os.argv[3])];
    try writePng(scratch, png_data, file_name);
}

const CheckArg = struct {
    const len = std.mem.len;
    fn isNaive() bool {
        const slice = std.os.argv[1][0..len(std.os.argv[1])];
        return std.mem.eql(u8, slice, "naive");
    }
    fn isRobust() bool {
        const slice = std.os.argv[1][0..len(std.os.argv[1])];
        return std.mem.eql(u8, slice, "robust");
    }
    fn orientTest() bool {
        const slice = std.os.argv[2][0..len(std.os.argv[2])];
        return std.mem.eql(u8, slice, "orient2d");
    }
    fn circleTest() bool {
        const slice = std.os.argv[2][0..len(std.os.argv[2])];
        return std.mem.eql(u8, slice, "incircle");
    }
};

fn Orient2DTests(T: type) type {
    return struct {
        const Ctx = lib.Context(T);
        const nextAfter = std.math.nextAfter;
        const inf = std.math.inf(T);

        fn run(comptime robust: bool, png_data: []u8) void {
            std.debug.assert(png_data.len == 3 * dim * dim);

            const cb = if (robust) Ctx.orient2D else Ctx.orient2DInexact;
            const p0 = Ctx.Point2D{ 0.5, 0.5 };
            const p1 = Ctx.Point2D{ 12, 12 };
            const p2 = Ctx.Point2D{ 24, 24 };

            var yd = p0[1];
            var row: usize = 0;
            while (row < dim) : (row += 1) {
                var xd = p0[0];
                var col: usize = 0;
                while (col < dim) : (col += 1) {
                    const p = Ctx.Point2D{ xd, yd };
                    const png_idx = (row * dim + col) * 3;
                    switch (cb(p1, p, p2)) {
                        .CounterClockwise => {
                            png_data[png_idx + 0] = 0xFF;
                            png_data[png_idx + 1] = 0xFF;
                            png_data[png_idx + 2] = 0xFF;
                        },
                        .Collinear => {
                            png_data[png_idx + 0] = 0xFF;
                            png_data[png_idx + 1] = 0;
                            png_data[png_idx + 2] = 0;
                        },
                        .Clockwise => {
                            png_data[png_idx + 0] = 0;
                            png_data[png_idx + 1] = 0;
                            png_data[png_idx + 2] = 0;
                        },
                    }
                    xd = std.math.nextAfter(T, xd, inf);
                }
                yd = std.math.nextAfter(T, yd, inf);
            }
        }
    };
}

fn writePng(scratch: std.mem.Allocator, png_data: []const u8, file_name: []const u8) !void {
    std.debug.assert(png_data.len == 3 * dim * dim);

    var image: zigimg.Image = try zigimg.Image.fromRawPixels(scratch, dim, dim, png_data, .rgb24);
    defer image.deinit();

    var file = try std.fs.cwd().createFile(file_name, .{});
    defer file.close();

    try image.flipVertically();
    try image.writeToFile(file, .{ .png = .{} });
}

fn usage(process_name: [*:0]u8) void {
    std.debug.print("Usage: {s} {{naive | robust}} {{incircle | orient2d}} <output.png>\n", .{process_name});
}

/// This imports the separate module containing `root.zig`. Take a look in `build.zig` for details.
const lib = @import("predicates-zig_lib");
