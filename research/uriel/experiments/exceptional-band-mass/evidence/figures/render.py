"""Draw the manuscript's three vector figures from packaged data, using ReportLab."""
import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

from reportlab.lib.colors import HexColor
from reportlab.pdfgen.canvas import Canvas

BASE = Path(__file__).resolve().parents[1]
TEAL, PLUM, INK, MUTE, GRID, OCHRE = "#09615B", "#794268", "#183831", "#4D625A", "#C6D6CE", "#8C571C"
WIDTH = 465


def label(c, x, y, s, size=9, color=MUTE, bold=False):
    c.setFillColor(HexColor(color))
    c.setFont("Helvetica-Bold" if bold else "Helvetica", size)
    c.drawString(x,y,s)


def line(c,x,y,xx,yy,color=GRID,width=.55):
    c.setStrokeColor(HexColor(color))
    c.setLineWidth(width)
    c.line(x,y,xx,yy)


def series(c, coords, color, width=1.6):
    p=c.beginPath()
    p.moveTo(*coords[0])
    for x,y in coords[1:]:
        p.lineTo(x,y)
    c.setStrokeColor(HexColor(color)); c.setLineWidth(width); c.drawPath(p)


def dot(c,x,y,color,r=2.2):
    c.setFillColor(HexColor(color))
    c.circle(x,y,r,stroke=0,fill=1)


def slide(out):
    data=json.loads((BASE/"primes/results.json").read_text())["rows"]
    c=Canvas(str(out/"slide.pdf"),pagesize=(WIDTH,225),invariant=1)
    X=lambda s: 38+414*math.log(s/256,2)/3
    Y=lambda p: 32+2.73*p
    for p in (0,10,20,30,40,50,60):
        line(c,38,Y(p),452,Y(p)); label(c,9,Y(p)-3,str(p)+"%",8)
    for s in (256,362,512,724,1024,1448,2048):
        label(c,X(s)-10,17,str(s),8)
    c.setDash(2.3,2); line(c,38,Y(25),451,Y(25),OCHRE,.75); c.setDash()
    for key,color in (("3/4",PLUM),("1/2",TEAL)):
        row=data[key]
        full=sum(map(float,row["full_mass"]))/2
        vals=[(X(s),Y(50*(float(l)+float(r))/full)) for s,l,r in row["plot_grid_step_16"]]
        series(c,vals,color)
        for kind in ("minimum","maximum"):
            ex=row["continuous_search"][kind]
            s=sum(map(float,ex["candidate_span"]))/2
            p=50*sum(map(float,ex["full_mass_share"]))
            dot(c,X(s),Y(p),color)
    label(c,38,211,"Share of all positive mass inside [s, 2s]",11,INK,True)
    label(c,195,196,"exponent 1/2",8,TEAL,True);label(c,260,196,"exponent 3/4",8,PLUM,True)
    label(c,325,196,"uniform share 25%",8,OCHRE)
    label(c,298,4,"band start s (logarithmic scale)",8)
    c.save()


def range_plot(out):
    data=json.loads((BASE/"geometry/results.json").read_text())["one_band_lambda2_B2"]
    c=Canvas(str(out/"range.pdf"),pagesize=(WIDTH,198),invariant=1)
    X=lambda J:45+365*(J-2)/6
    Y=lambda f:32+116*f
    for v in (0,.25,.5,.75,1):
        line(c,45,Y(v),415,Y(v));label(c,12,Y(v)-3,f"{int(100*v)}%",8)
    for j in (2,3,4,5,6,7,8):
        label(c,X(j)-2,17,str(j),8)
    pts=[]
    for i in range(401):
        r=1+3*i/400
        # lambda=B=2; for r>=1 the (4-r)/(2+r) branch is active after r=1.
        f=max(0,min(1,(4-r)/(2+r),2/(r+1)))
        pts.append((X(2*r),Y(f)))
    series(c,pts,TEAL)
    for row in data:
        j=float(Fraction(row["J"])); p=float(Fraction(row["fraction"]))
        if 2<=j<=8:
            r=j/2
            assert abs(p-max(0,min(1,(4-r)/(2+r),2/(r+1)))) < 1e-12
            dot(c,X(j),Y(p),TEAL)
    label(c,39,177,"One exceptional label, movable window",11,INK,True)
    label(c,39,161,"Minimum contaminated share under worst placement of the label",9)
    label(c,235,4,"available range parameter J",8)
    c.save()


def chords(out):
    c=Canvas(str(out/"tents.pdf"),pagesize=(WIDTH,155),invariant=1)
    for i,(prime,sgn) in enumerate(((487,1),(509,-1))):
        x0=42+222*i; yc=71
        line(c,x0,yc,x0+169,yc,GRID,.9)
        series(c,[(x0,yc),(x0+84.5,yc+sgn*38),(x0+169,yc)],TEAL if sgn==1 else PLUM,1.9)
        for j,n in enumerate((prime-1,prime,prime+1)):
            label(c,x0+j*84.5-8,16,str(n),8)
        label(c,x0+15,121,"downward slope jump" if sgn==1 else "upward slope jump",9,INK,True)
    label(c,27,142,"Difference between the smoothed sum and its endpoint chord",11,INK,True)
    label(c,32,4,"The vertical unit in each panel is half the magnitude of its own slope jump.",8)
    c.save()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    dest=parser.parse_args().destination
    dest.mkdir(parents=True,exist_ok=True)
    slide(dest);range_plot(dest);chords(dest)


if __name__=="__main__":
    main()
