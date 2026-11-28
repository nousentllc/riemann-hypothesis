from math import sin,cos,exp,log,sqrt,pi
from pathlib import Path
import json
from reportlab.pdfgen.canvas import Canvas
from reportlab.lib.colors import HexColor
b=Path(__file__).resolve().parent;root=b.parent
res=json.loads((root/'models/results.json').read_text())
green='#11645C';plum='#783F63';ink='#203C38';muted='#475B58';line='#C9D7D0';rust='#93471E'
def tx(c,x,y,text,s=10,color=ink,ft='Helvetica'):
 c.setFillColor(HexColor(color));c.setFont(ft,s);c.drawString(x,y,text)
def ln(c,xa,ya,xb,yb,col=line,lw=.55):
 c.setStrokeColor(HexColor(col));c.setLineWidth(lw);c.line(xa,ya,xb,yb)
def drawline(c,xy,col,lw=1.3):
 p=c.beginPath();p.moveTo(*xy[0])
 for x,y in xy[1:]:p.lineTo(x,y)
 c.setLineWidth(lw);c.setStrokeColor(HexColor(col));c.drawPath(p,stroke=1,fill=0)
def pt(c,x,y,col):
 c.setFillColor(HexColor(col));c.circle(x,y,2.2,stroke=0,fill=1)
def canvas(k,H=210):return Canvas(str(b/(k+'.pdf')),pagesize=(468,H),invariant=1)
def primedata():
 c=canvas('actual')
 v=[0.]*4097
 for p in range(2,len(v)):
  if any(p%d==0 for d in range(2,int(sqrt(p))+1)):continue
  j=p
  while j<len(v):
   v[j]=log(p)*([0,1,0,-1][j%4]);j*=p
 a=.24560958477731415;d=0.;arr=[]
 for n in range(2,4097):
  a+=v[n]/n;d+=v[n]
  if n>=256:arr.append((n,(a*n-d)/sqrt(n)))
 x=lambda n:39+387*log(n/256)/log(16)
 y=lambda z:109+475*z
 for t in (-.15,-.1,-.05,0,.05,.1,.15):
  ln(c,39,y(t),429,y(t));tx(c,4,y(t)-3,f'{t:.2f}',8,muted)
 for n in [256,512,1024,2048,4096]:tx(c,x(n)-9,10,str(n),8,muted)
 p=c.beginPath();p.moveTo(x(256),y(0))
 for n,z in arr:p.lineTo(x(n),y(max(0,z)))
 p.lineTo(x(4096),y(0));p.close();c.setFillColor(HexColor('#D0E8DF'));c.drawPath(p,fill=1,stroke=0)
 ln(c,39,y(0),430,y(0),'#758781');drawline(c,[(x(n),y(z)) for n,z in arr],green,.85)
 zn=dict(arr)[487];pt(c,x(487),y(zn),plum);tx(c,x(487)+6,y(zn)+1,'487',8,plum)
 tx(c,39,192,'Real character modulo four',11,ink,'Helvetica-Bold');tx(c,265,192,'Normalized sum, horizontal log scale',8,muted)
 c.save()
def phases():
 c=canvas('phase')
 rows=res['oscillatory']['rows']
 x=lambda i:45+58*i;y=lambda v:31+92*v
 for t in (0,.4,.8,1.2,1.6):
  ln(c,45,y(t),400,y(t));tx(c,16,y(t)-3,f'{t:.1f}',8,muted)
 upper=[];lower=[]
 for i,r in enumerate(rows):
  xx=x(i);tx(c,xx-3,17,str(r['U']),8,muted)
  upper.append((xx,y(r['scaled_max_sample'])));lower.append((xx,y(r['scaled_min_sample'])))
 for pts,col in ((upper,plum),(lower,green)):
  drawline(c,pts,col,1.6)
  for xx,yy in pts:pt(c,xx,yy,col)
 for t,col in ((res['oscillatory']['min_H'],green),(res['oscillatory']['max_H'],plum)):
  c.setDash(2,2);ln(c,45,y(t),402,y(t),col,.65);c.setDash()
 tx(c,402,y(1.53),'max',8,plum);tx(c,402,y(1.0)-3,'min',8,green)
 tx(c,45,192,'Positive mass divided by terminal exponential',11,ink,'Helvetica-Bold');tx(c,298,2,'U = log Y (doubling)',8,muted);c.save()
def widths():
 c=canvas('widths')
 x=lambda u:42+2.49*u;y=lambda z:88+4.5*z
 for t in (-14,-7,0,7,14,21):
  ln(c,52,y(t),370,y(t));tx(c,20,y(t)-3,str(t),8,muted)
 for u in (4,16,32,64,96,128):tx(c,x(u)-5,14,str(u),8,muted)
 colors=(plum,rust,green)
 for j,case in enumerate(res['spikes']):
  r=case['rows'][::2]
  xy=[(x(v['U']),y(log(v['mass'])/log(10))) for v in r];drawline(c,xy,colors[j]);tx(c,369,xy[-1][1]-3,'b = '+str(case['width_exponent']),8,colors[j])
  for xx,yy in xy:pt(c,xx,yy,colors[j])
 xy=[(x(v['U']),y(log(v['normalized_peak'])/log(10))) for v in r]
 c.setDash(3,2);drawline(c,xy,ink);c.setDash();tx(c,369,xy[-1][1]-3,'all peaks',8,ink)
 tx(c,41,193,'Same peak height, different positive mass',11,ink,'Helvetica-Bold');tx(c,42,178,'Vertical axis: base-10 logarithm',8,muted);tx(c,292,1,'U = log Y',8,muted);c.save()
primedata();phases();widths()

