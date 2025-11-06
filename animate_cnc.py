import svgpathtools
import drawsvg as draw
import imageio.v3 as iio
import cairosvg
from PIL import Image
import io
from tqdm import tqdm
import os
import re
import argparse
import math
import xml.etree.ElementTree as ET
from svgpathtools import parse_path, Path, Line, CubicBezier, QuadraticBezier, Arc
import numpy as np

# Define o namespace SVG para facilitar a busca por elementos
SVG_NS = "{http://www.w3.org/2000/svg}"

# --- Configurações Globais (Mantidas) ---
COLOR_BACKGROUND_PATH = '#AAAAAA'
COLOR_MACHINED_PATH_DEFAULT = '#0000FF'
COLOR_TOOL_DEFAULT = '#FF0000'
COLOR_CANVAS_BACKGROUND = '#FFFFFF'

TOOL_TIP_OFFSET = complex(0, 0) 
TOOL_STROKE_WIDTH = 2.0
PATH_STROKE_WIDTH = 2.0
GLOBAL_Y_INVERTED = False
GLOBAL_Y_SCALE = 1

# --- FUNÇÕES DE TRANSFORMAÇÃO E PARSING (Mantidas) ---

def apply_transform(path, matrix):
    a, b, c, d, e, f = matrix
    def transform_point(p):
        x = p.real
        y = p.imag
        new_x = a * x + c * y + e
        new_y = b * x + d * y + f
        new_y = new_y * GLOBAL_Y_SCALE
        if GLOBAL_Y_INVERTED:
            new_y = -new_y
        return complex(new_x, new_y)
    new_segments = []
    for seg in path:
        new_start = transform_point(seg.start)
        new_end = transform_point(seg.end)
        if isinstance(seg, Line):
            new_segments.append(Line(new_start, new_end))
        elif isinstance(seg, CubicBezier):
            new_c1 = transform_point(seg.control1)
            new_c2 = transform_point(seg.control2)
            new_segments.append(CubicBezier(new_start, new_c1, new_c2, new_end))
        elif isinstance(seg, QuadraticBezier):
            new_c = transform_point(seg.control)
            new_segments.append(QuadraticBezier(new_start, new_c, new_end))
        elif isinstance(seg, Arc):
            new_sweep = seg.sweep
            if GLOBAL_Y_INVERTED:
                new_sweep = not seg.sweep
            R_x_original = seg.radius.real
            R_y_original = seg.radius.imag
            new_R_x = a * R_x_original
            new_R_y = d * R_y_original
            if GLOBAL_Y_SCALE != 0:
                new_R_y = new_R_y / GLOBAL_Y_SCALE
            new_radius = complex(abs(new_R_x), abs(new_R_y))
            new_segments.append(Arc(new_start, new_radius, seg.rotation,
                                         seg.large_arc, new_sweep, new_end))
        else:
            new_segments.append(Line(new_start, new_end))
    return Path(*new_segments)


def parse_group_transform(transform_str):
    global GLOBAL_Y_INVERTED
    a, b, c, d, e, f = 1, 0, 0, 1, 0, 0
    GLOBAL_Y_INVERTED = False
    transform_str = transform_str.replace('\xa0', ' ')
    match_s = re.search(r'scale\(([^)\s]+)\)', transform_str)
    if match_s:
        s = float(match_s.group(1))
        a *= s
        d *= s
    if 'scale(1 -1)' in transform_str:
        GLOBAL_Y_INVERTED = True
        d = abs(d)
    match_matrix = re.search(r'matrix\(([^)]+)\)', transform_str)
    if match_matrix:
        matrix_vals_str = match_matrix.group(1).split(',')
        if len(matrix_vals_str) == 6:
            m_a, m_b, m_c, m_d, m_e, m_f = [float(x.strip()) for x in matrix_vals_str]
            a = m_a * a
            b = m_b
            c = m_c
            d = m_d * d
            e += m_e
            f += m_f
            if m_d < 0 and not GLOBAL_Y_INVERTED:
                GLOBAL_Y_INVERTED = True
                d = abs(d)
    match_t = re.search(r'translate\(([^,)\s]+)\s+([^,)]+)\)', transform_str)
    if match_t:
        tx = float(match_t.group(1))
        ty = float(match_t.group(2))
        e += tx
        f += ty
    
    # Neutraliza a translação
    e = 0
    f = 0

    return (a, b, c, d, e, f)


def get_style_value(style_str, prop):
    match = re.search(fr'{prop}:\s*([^;]+)', style_str)
    if match:
        return match.group(1).strip()
    return None

def get_path_style(attrs, default_stroke=None):
    style_str = attrs.get('style', '').replace(' ', '')
    stroke = get_style_value(style_str, 'stroke')
    stroke_width = get_style_value(style_str, 'stroke-width')
    opacity = get_style_value(style_str, 'opacity')
    stroke_opacity = get_style_value(style_str, 'stroke-opacity')

    if stroke is None: stroke = attrs.get('stroke', default_stroke)
    if stroke_width is None: stroke_width = attrs.get('stroke-width', None)
    if opacity is None: opacity = attrs.get('opacity', '1')
    if stroke_opacity is None: stroke_opacity = attrs.get('stroke-opacity', '1')
    if stroke == 'none': stroke = None
    return stroke, stroke_width, opacity, stroke_opacity

def is_tool_profile(attrs):
    stroke, stroke_width, opacity, stroke_opacity = get_path_style(attrs)
    tolerance = 0.001
    try:
        if float(opacity) <= tolerance: return True
    except (ValueError, TypeError): pass
    try:
        if float(stroke_opacity) <= tolerance: return True
    except (ValueError, TypeError): pass
    try:
        if stroke_width is not None and float(stroke_width) <= tolerance: return True
    except (ValueError, TypeError): pass
    return False

def parse_svg_to_layers(svg_file):
    all_transformed_paths = []
    layers_data = []
    background_paths = [] 

    try:
        with open(svg_file, 'r', encoding='utf-8') as f:
            content = f.read().replace('\xa0', ' ')
        root = ET.fromstring(content)
    except Exception as e:
        print(f"Erro ao analisar o XML do SVG: {e}")
        return [], [], []

    namespaces = {'svg': SVG_NS.strip('{}'), 'inkscape': 'http://www.inkscape.org/namespaces/inkscape'}

    layer_groups = root.findall('svg:g[@inkscape:groupmode="layer"]', namespaces)

    if not layer_groups:
        layer_groups = root.findall('svg:g', namespaces)
        if not layer_groups:
             layer_groups = [root]
        else:
             pass

    layer_counter = 1

    for group in layer_groups:
        transform_str = group.get('transform', "")
        transform_matrix = parse_group_transform(transform_str)
        paths_in_group = group.findall('.//svg:path', namespaces)

        group_tool_data = None
        group_machining_paths = []
        paths_without_tool = [] 

        for path_element in paths_in_group:
            attrs = dict(path_element.items())
            d_str = attrs.get('d')
            if not d_str:
                continue

            raw_path = parse_path(d_str.replace('\xa0', ' '))
            transformed_path = apply_transform(raw_path, transform_matrix)
            all_transformed_paths.append(transformed_path)

            stroke, _, _, _ = get_path_style(attrs, default_stroke=COLOR_TOOL_DEFAULT)
            is_tool_candidate = is_tool_profile(attrs)

            if is_tool_candidate and not group_tool_data:
                tool_color = stroke if stroke is not None else COLOR_TOOL_DEFAULT
                group_tool_data = {
                    'path': transformed_path,
                    'color': tool_color,
                    'attrs': attrs
                }
            elif not is_tool_candidate:
                path_color = stroke if stroke is not None else COLOR_MACHINED_PATH_DEFAULT
                path_data = {
                    'path': transformed_path,
                    'color': path_color,
                    'attrs': attrs
                }
                
                if group_tool_data:
                    group_machining_paths.append(path_data)
                else:
                    paths_without_tool.append(path_data)
        
        if group_tool_data and group_machining_paths:
            layers_data.append({
                'tool': group_tool_data,
                'paths': group_machining_paths,
                'machining_color': group_machining_paths[0]['color'] if group_machining_paths else COLOR_MACHINED_PATH_DEFAULT,
                'name': f"Camada {layer_counter} (Grupo: {group.get('id', 'N/A')})"
            })
            layer_counter += 1
            
        elif paths_without_tool:
            background_paths.extend(paths_without_tool)

    return layers_data, all_transformed_paths, background_paths

# --- FUNÇÕES DE AJUDA PARA CHECAGEM DE INTERSEÇÃO (Mantidas) ---

def is_segment_in_box(segment, zoom_box):
    min_x, min_y, max_x, max_y = zoom_box
    seg_min_x, seg_max_x, seg_min_y, seg_max_y = segment.bbox()
    
    if seg_min_x >= max_x or seg_max_x <= min_x or \
       seg_min_y >= max_y or seg_max_y <= min_y:
        return False
        
    return True

# --- FUNÇÕES DE RENDERIZAÇÃO (Mantidas) ---

def create_base_drawing(viewBox_str, render_w, render_h):
    d = draw.Drawing(render_w, render_h)
    d.view_box = [float(v) for v in viewBox_str.split()]
    vb = d.view_box
    d.append(draw.Rectangle(vb[0], vb[1], vb[2], vb[3], fill=COLOR_CANVAS_BACKGROUND))
    return d

def render_frames_to_files(frames, output_base, fps, render_w, render_h, formats):
    requested_mp4 = 'mp4' in formats
    requested_gif = 'gif' in formats

    if not requested_mp4 and not requested_gif:
        print("Nenhum formato de saída válido solicitado.")
        return False

    print(f"\nRenderizando {len(frames)} frames...")
    pil_images = []

    try:
        def frame_generator():
            for d_frame in frames:
                png_bytes = cairosvg.svg2png(
                    bytestring=d_frame.as_svg().encode('utf-8'),
                    output_width=render_w,
                    output_height=render_h
                )
                img = Image.open(io.BytesIO(png_bytes))
                img = img.convert("RGB") 
                
                yield img

        for img in tqdm(frame_generator(), total=len(frames), desc="Processando Frames"):
            pil_images.append(img)

        # Geração do MP4
        if requested_mp4:
            output_mp4 = f"{output_base}.mp4"
            print(f"Salvando {output_mp4}...")
            iio.imwrite(
                output_mp4,
                pil_images,
                fps=fps,
                codec='libx264',
                quality=6 
            )

        # Geração do GIF
        if requested_gif:
            output_gif = f"{output_base}.gif"
            print(f"Salvando {output_gif}...")
            
            gif_frames = pil_images[::3]
            
            iio.imwrite(
                output_gif,
                gif_frames,
                duration=(1000 / fps),
                loop=0,
                quantizer='wu', 
                optimize=True 
            )
        
        return True

    except Exception as e:
        print(f"Erro fatal na renderização. Certifique-se de que `cairosvg` e `imageio[ffmpeg]` estão instalados: {e}")
        print("Instale-os via: pip install cairosvg imageio[ffmpeg]")
        return False


def main(args):
    global TOOL_STROKE_WIDTH, PATH_STROKE_WIDTH, GLOBAL_Y_INVERTED
    global TOOL_TIP_OFFSET 

    # Processa argumentos
    TOOL_STROKE_WIDTH = args.tool_stroke
    PATH_STROKE_WIDTH = args.path_stroke
    TOOL_TIP_OFFSET = complex(0, 0)
    
    # Processamento dos formatos de saída
    requested_formats = [f.strip().lower() for f in args.format.split(',') if f.strip().lower() in ('mp4', 'gif')]

    if not requested_formats:
        requested_formats = ['mp4', 'gif']
    
    # Processamento do Zoombox
    zoom_box = None
    if args.zoom_box:
        try:
            parts = [float(p.strip()) for p in args.zoom_box.replace('x', ',').split(',')]
            if len(parts) == 4:
                zoom_box = (parts[0], parts[1], parts[2], parts[3])
            else:
                raise ValueError("Formato de zoom-box incorreto.")
        except ValueError:
            zoom_box = None
            
    # Processamento SVG, ViewBox, Resolução (Mantido)
    try:
        layers_data, all_transformed_paths, background_paths = parse_svg_to_layers(args.svg)
    except FileNotFoundError:
        print(f"Erro: Arquivo SVG de entrada '{args.svg}' não encontrado.")
        return

    if not all_transformed_paths:
        min_x, min_y, max_x, max_y = 0, 0, 100, 100
    else:
        min_x, max_x, min_y, max_y = svgpathtools.Path(*all_transformed_paths).bbox()

    MARGIN = 5.0
    vb_min_x = min_x - MARGIN
    vb_min_y = min_y - MARGIN
    vb_width = (max_x - min_x) + 2 * MARGIN
    vb_height = (max_y - min_y) + 2 * MARGIN
    
    if zoom_box:
        vb_min_x = zoom_box[0] - MARGIN
        vb_min_y = zoom_box[1] - MARGIN
        vb_width = (zoom_box[2] - zoom_box[0]) + 2 * MARGIN
        vb_height = (zoom_box[3] - zoom_box[1]) + 2 * MARGIN
        
    render_w = max(400, int(vb_width))
    render_h = max(400, int(vb_height))
    
    if args.resolution:
        try:
            res_parts = args.resolution.replace('x', ',').split(',')
            if len(res_parts) == 2:
                res_w = int(res_parts[0].strip())
                res_h = int(res_parts[1].strip())
                if res_w > 0 and res_h > 0:
                    render_w = res_w
                    render_h = res_h
        except ValueError:
            pass
            
    # Ajuste de Aspect Ratio (Mantido)
    render_aspect = render_w / render_h
    view_aspect = vb_width / vb_height
    
    if abs(view_aspect - render_aspect) > 0.001:
        if view_aspect > render_aspect:
            new_vb_height = vb_width / render_aspect
            delta_h = (new_vb_height - vb_height) / 2
            vb_min_y -= delta_h
            vb_height = new_vb_height
        else:
            new_vb_width = vb_height * render_aspect
            delta_w = (new_vb_width - vb_width) / 2
            vb_min_x -= delta_w
            vb_width = new_vb_width
            
    viewBox_str = f"{vb_min_x} {vb_min_y} {vb_width} {vb_height}"
    
    # --- INÍCIO DA SIMULAÇÃO (Mantida) ---
    all_frames = []
    completed_paths_global = []

    for layer_index, layer in enumerate(layers_data):
        machining_paths_data = layer['paths']
        tool_shape = layer['tool']['path']
        tool_color = layer['tool']['color']
        machining_color = layer['machining_color']
        tool_d_string = tool_shape.d()
        
        for path_index, m_path_data in enumerate(machining_paths_data):
            m_path = m_path_data['path']
            current_path_segments = []

            for segment_index, segment in enumerate(m_path):
                segment_length = segment.length()
                if segment_length < 1e-6:
                    current_path_segments.append(segment)
                    continue

                simulate_segment = True
                if zoom_box:
                    if not is_segment_in_box(segment, zoom_box):
                        simulate_segment = False

                if simulate_segment:
                    duration_s = segment_length / args.speed
                    num_steps = max(2, int(math.ceil(duration_s * args.fps))) 
                    
                    for i in range(num_steps + 1):
                        t = i / num_steps
                        d_frame = create_base_drawing(viewBox_str, render_w, render_h)
                        
                        # Desenho de fundo, futuro e usinado
                        for bg_path_data in background_paths:
                            d_frame.append(draw.Path(d=bg_path_data['path'].d(), stroke=bg_path_data['color'], stroke_width=PATH_STROKE_WIDTH, fill='none'))
                        for future_path_data in machining_paths_data[path_index + 1:]:
                            d_frame.append(draw.Path(d=future_path_data['path'].d(), stroke=COLOR_BACKGROUND_PATH, stroke_width=PATH_STROKE_WIDTH, fill='none'))
                        for future_segment in m_path[segment_index+1:]:
                            d_frame.append(draw.Path(d=Path(future_segment).d(), stroke=COLOR_BACKGROUND_PATH, stroke_width=PATH_STROKE_WIDTH, fill='none'))
                        if t < 1.0:
                            partial_future_seg = segment.cropped(t, 1.0)
                            d_frame.append(draw.Path(d=Path(partial_future_seg).d(), stroke=COLOR_BACKGROUND_PATH, stroke_width=PATH_STROKE_WIDTH, fill='none'))
                        for p in completed_paths_global:
                            d_frame.append(draw.Path(d=p['path'].d(), stroke=p['color'], stroke_width=PATH_STROKE_WIDTH, fill='none'))
                        for s in current_path_segments:
                            d_frame.append(draw.Path(d=Path(s).d(), stroke=machining_color, stroke_width=PATH_STROKE_WIDTH, fill='none'))
                        if t > 0:
                            partial_segment = segment.cropped(0, t)
                            d_frame.append(draw.Path(d=Path(partial_segment).d(), stroke=machining_color, stroke_width=PATH_STROKE_WIDTH, fill='none'))

                        # Desenha a Ferramenta 
                        current_pos = segment.point(t)
                        dx = current_pos.real - TOOL_TIP_OFFSET.real 
                        dy = current_pos.imag - TOOL_TIP_OFFSET.imag
                        d_frame.append(draw.Path(d=tool_d_string, stroke=tool_color, stroke_width=TOOL_STROKE_WIDTH, fill='none', transform=f'translate({dx}, {dy})'))
                        all_frames.append(d_frame)
                    
                    current_path_segments.append(segment)
                
                else:
                    current_path_segments.append(segment)
            
            completed_paths_global.append({'path': m_path, 'color': machining_color})
            
    # Geração dos arquivos de saída
    if all_frames:
        success = render_frames_to_files(all_frames, args.output, args.fps, render_w, render_h, requested_formats)
        if success:
            print(f"\nSucesso! Os arquivos de animação solicitados foram salvos com o prefixo '{args.output}'.")
        else:
            print(f"\nFalha na renderização de um ou mais formatos solicitados.")
    else:
        print("Nenhum frame gerado.")


if __name__ == "__main__":
    
    # --- EPILOG COM EXEMPLOS DE USO ---
    EXAMPLES = """
Exemplos de Uso:
  # Uso Básico: Gera MP4 e GIF com as configurações padrão.
  python script.py --svg profile.svg --output simulacao

  # Gera apenas MP4, em alta resolução, a 60 fps e simulação mais rápida.
  python script.py --svg profile.svg --output video_rapido --format mp4 --resolution 1920,1080 --fps 60 --speed 200.0

  # Simula APENAS a região de 0 a 50 em X, e 0 a 50 em Y (modo zoom)
  python script.py --svg profile.svg --output detalhe_zoom --zoom-box "0,0,50,50"
  
  # Gera apenas o GIF
  python script.py --svg profile.svg --output animacao_web --format gif

"""
    # --- ARGUMENT PARSER ---
    parser = argparse.ArgumentParser(
        description="Simulador de Usinagem 2D para Torno CNC. Processa caminhos SVG, neutraliza offsets de grupo e gera animação.",
        formatter_class=argparse.RawTextHelpFormatter, # Permite quebrar linha no epilog
        epilog=EXAMPLES
    )
    
    parser.add_argument('--svg', required=True, help="Caminho para o arquivo SVG de entrada (perfil da ferramenta + caminhos).")
    parser.add_argument('--output', required=True, help="Nome base para os arquivos de saída (ex: 'simulacao').")
    
    parser.add_argument('--fps', type=int, default=30, help="Frames por segundo da animação final.")
    parser.add_argument('--speed', type=float, default=100.0, help="Velocidade da ferramenta em 'unidades do viewBox' por segundo.")
    
    # CONTROLE DE SAÍDA E RESOLUÇÃO
    parser.add_argument('--format', type=str, default='mp4,gif', 
                        help="Formatos de saída separados por vírgula. Opções: 'mp4', 'gif', ou 'mp4,gif'.")
                        
    parser.add_argument('--resolution', type=str, default=None, 
                        help="Resolução de saída fixa no formato 'Largura,Altura' ou 'LarguraxAltura' (ex: '1280,720').")
                        
    parser.add_argument('--zoom-box', type=str, default=None, 
                        help="Região de zoom e simulação restrita no formato 'min_x, min_y, max_x, max_y' (ex: '0,0,50,50').")
                        
    # ESTILOS
    parser.add_argument('--tool-stroke', type=float, default=2.0, 
                        help="Espessura do traço (stroke-width) do perfil da ferramenta.")
    parser.add_argument('--path-stroke', type=float, default=2.0, 
                        help="Espessura do traço (stroke-width) dos caminhos usinados (futuro e passado).")
    
    parsed_args = parser.parse_args()
    main(parsed_args)
