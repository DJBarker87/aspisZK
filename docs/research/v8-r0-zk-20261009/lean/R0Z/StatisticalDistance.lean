import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.NormNum
-- Unified-base import set (LOG D65 follow-up): this module was Version: ImageMagick 7.1.2-19 Q16-HDRI aarch64 23897 https://imagemagick.org
Copyright: (C) 1999 ImageMagick Studio LLC
License: https://imagemagick.org/license/
Features: Cipher DPC HDRI Modules 
Delegates (built-in): bzlib freetype heic jng jpeg lcms ltdl lzma png tiff webp xml zlib zstd
Compiler: clang (21.0.0)
Usage: import [options ...] [ file ]

Image Settings:
  -adjoin              join images into a single multi-image file
  -border              include window border in the output image
  -channel type        apply option to select image channels
  -colorspace type     alternate image colorspace
  -comment string      annotate image with comment
  -compress type       type of pixel compression when writing the image
  -define format:option
                       define one or more image format options
  -density geometry    horizontal and vertical density of the image
  -depth value         image depth
  -descend             obtain image by descending window hierarchy
  -display server      X server to contact
  -dispose method      layer disposal method
  -dither method       apply error diffusion to image
  -delay value         display the next image after pausing
  -encipher filename   convert plain pixels to cipher pixels
  -endian type         endianness (MSB or LSB) of the image
  -encoding type       text encoding type
  -filter type         use this filter when resizing an image
  -format "string"     output formatted image characteristics
  -frame               include window manager frame
  -gravity direction   which direction to gravitate towards
  -identify            identify the format and characteristics of the image
  -interlace type      None, Line, Plane, or Partition
  -interpolate method  pixel color interpolation method
  -label string        assign a label to an image
  -limit type value    Area, Disk, Map, or Memory resource limit
  -monitor             monitor progress
  -page geometry       size and location of an image canvas
  -pause seconds       seconds delay between snapshots
  -pointsize value     font point size
  -quality value       JPEG/MIFF/PNG compression level
  -quiet               suppress all warning messages
  -regard-warnings     pay attention to warning messages
  -repage geometry     size and location of an image canvas
  -respect-parentheses settings remain in effect until parenthesis boundary
  -sampling-factor geometry
                       horizontal and vertical sampling factor
  -scene value         image scene number
  -screen              select image from root window
  -seed value          seed a new sequence of pseudo-random numbers
  -set property value  set an image property
  -silent              operate silently, i.e. don't ring any bells 
  -snaps value         number of screen snapshots
  -support factor      resize support: > 1.0 is blurry, < 1.0 is sharp
  -synchronize         synchronize image to storage device
  -taint               declare the image as modified
  -transparent-color color
                       transparent color
  -treedepth value     color tree depth
  -verbose             print detailed information about the image
  -virtual-pixel method
                       Constant, Edge, Mirror, or Tile
  -window id           select window with this id or name
                       root selects whole screen

Image Operators:
  -annotate geometry text
                       annotate the image with text
  -colors value        preferred number of colors in the image
  -crop geometry       preferred size and location of the cropped image
  -encipher filename   convert plain pixels to cipher pixels
  -extent geometry     set the image size
  -geometry geometry   preferred size or location of the image
  -help                print program options
  -monochrome          transform image to black and white
  -negate              replace every pixel with its complementary color 
  -quantize colorspace reduce colors in this colorspace
  -resize geometry     resize the image
  -rotate degrees      apply Paeth rotation to the image
  -strip               strip image of all profiles and comments
  -thumbnail geometry  create a thumbnail of the image
  -transparent color   make this color transparent within the image
  -trim                trim image edges
  -type type           image type

Miscellaneous Options:
  -debug events        display copious debugging information
  -help                print program options
  -list type           print a list of supported option arguments
  -log format          format of debugging information
  -version             print version information

By default, 'file' is written in the MIFF image format.  To
specify a particular image format, precede the filename with an image
format name and a colon (i.e. ps:image) or specify the image type as
the filename suffix (i.e. image.ps).  Specify 'file' as '-' for
standard input or output., and the 93
-- privacy modules above it relied on that.  The set below replaces it for them; it is the
-- linear-algebra / finite-field / big-operator / tactic layer they use, not all of Mathlib.
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Finite uniform tapes, arbitrary output types, and rational total variation.
All finite sums below are symbolic. No concrete tape/state/trace is evaluated. -/
set_option autoImplicit false
namespace R0Z
noncomputable section
open scoped BigOperators

variable {R T U V : Type}

/-- Uniform expectation over a finite tape. Security statements also require
`Nonempty` tapes; there is no conditioning on successful execution. -/
def mean [Fintype R] (f : R → ℚ) : ℚ := (∑ r, f r) / Fintype.card R

def law [Fintype R] (f : R → V) (v : V) : ℚ := by
  classical
  exact mean (fun r => if f r = v then 1 else 0)

def support [Fintype R] (f : R → V) : Finset V := by
  classical
  exact Finset.univ.image f

private theorem law_zero [Fintype R] (f : R → V) (v : V)
    (hv : v ∉ support f) : law f v = 0 := by
  classical
  have hn : ∀ r, f r ≠ v := by
    intro r he
    exact hv (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, he⟩)
  simp only [law, mean, if_neg (hn _), Finset.sum_const_zero, zero_div]

/-- Standard total variation: half the L1 difference on the union of supports.
The output need not be finite (e.g. messages include arbitrary polynomials). -/
def dist [Fintype R] [Fintype T] (f : R → V) (g : T → V) : ℚ := by
  classical
  exact (∑ v ∈ support f ∪ support g, |law f v - law g v|) / 2

def EqualLaws [Fintype R] [Fintype T] (f : R → V) (g : T → V) : Prop :=
  ∀ v, law f v = law g v

theorem dist_nonneg [Fintype R] [Fintype T] (f : R → V) (g : T → V) :
    0 ≤ dist f g := by
  classical
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem dist_zero_of_equalLaws [Fintype R] [Fintype T]
    (f : R → V) (g : T → V) (h : EqualLaws f g) : dist f g = 0 := by
  classical
  unfold dist
  have hz : ∀ v, |law f v - law g v| = 0 := fun v => by rw [h v, sub_self, abs_zero]
  simp only [hz, Finset.sum_const_zero, zero_div]

private theorem dist_on [Fintype R] [Fintype T]
    (f : R → V) (g : T → V) (s : Finset V)
    (hf : support f ⊆ s) (hg : support g ⊆ s) :
    dist f g = (∑ v ∈ s, |law f v - law g v|) / 2 := by
  classical
  unfold dist
  congr 1
  apply Finset.sum_subset (Finset.union_subset hf hg)
  intro v _ hn
  have hf' : v ∉ support f := fun h => hn (Finset.mem_union_left _ h)
  have hg' : v ∉ support g := fun h => hn (Finset.mem_union_right _ h)
  rw [law_zero f v hf', law_zero g v hg', sub_self, abs_zero]

theorem dist_triangle [Fintype R] [Fintype T] [Fintype U]
    (f : R → V) (g : T → V) (h : U → V) :
    dist f h ≤ dist f g + dist g h := by
  classical
  let s := (support f ∪ support g) ∪ support h
  have hf : support f ⊆ s := fun _ hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hg : support g ⊆ s := fun _ hv =>
    Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hh : support h ⊆ s := fun _ hv => Finset.mem_union_right _ hv
  rw [dist_on f h s hf hh, dist_on f g s hf hg, dist_on g h s hg hh, ← add_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun v _ => abs_sub_le (law f v) (law g v) (law h v))

#print axioms mean
#print axioms law
#print axioms support
#print axioms law_zero
#print axioms dist
#print axioms EqualLaws
#print axioms dist_nonneg
#print axioms dist_zero_of_equalLaws
#print axioms dist_on
#print axioms dist_triangle
end
end R0Z
